#ifndef __Infer_H
#define __Infer_H

//These functions will do very basic inference of constant types for now.
#include "basetypes.h"
#include "parse_misc.h"
#include "sectypes.h"
#include "Module.h"
#include "PGate.h"
#include "PWire.h"

class ConstraintSolver {

public:
    ConstraintSolver() {}
    virtual ~ConstraintSolver() {}

    /**
     * Given a set of constraints, map each type variable to a label such that
     * all of the constraints are satisfied.
     */
    virtual map<perm_string, SecType*> infer(unordered_set<Constraint*> &constraints) {
        map<perm_string, SecType*> assignments;
        return inferLabels(constraints, assignments);
    }

    /**
     * Given a set of constraints, map each type variable to a label such that
     * all of the constraints are satisfied.
     */
    virtual map<perm_string, SecType*> inferLabels(unordered_set<Constraint*> &constraints,
        map<perm_string, SecType*> &initAssgns) = 0;
};

class RestrictiveSolver : public ConstraintSolver {
public:
    RestrictiveSolver() {}
    virtual ~RestrictiveSolver() {}
    /**
     * Use the iterative algorithm from the decentralized label paper to
     * infer assignments from type variables to labels.
    */
    virtual map<perm_string, SecType*> inferLabels(unordered_set<Constraint*> &constraints,
        map<perm_string, SecType*> &initAssgns);
};

class PermissiveSolver : public ConstraintSolver {
public:
    PermissiveSolver() {}
    virtual ~PermissiveSolver() {}
    /**
     * Use the iterative algorithm from the Viadcut paper
     * infer assignments from type variables to labels.
     */
    virtual map<perm_string, SecType*> inferLabels(unordered_set<Constraint*> &constraints,
        map<perm_string, SecType*> &initAssgns);
};

//This class uses a set of type variables as 'inputs'
//And infers all constraints in terms of those labels
class InterfaceSolver : public ConstraintSolver {
public:
    //This class owns the reference to its solver so delete it during de-allocation
    InterfaceSolver(ConstraintSolver* c) : _baseSolver(c) {};
    virtual ~InterfaceSolver() { delete _baseSolver; }
    virtual map<perm_string, SecType*> infer(unordered_set<Constraint*> &constraints) {
        std::map<perm_string, SecType*> assignments;
        for (auto in : _inputNames) {
            assignments[in] = new ConstType(in, true);
        }
        return inferLabels(constraints, assignments);
    }

    virtual map<perm_string, SecType*> inferLabels(unordered_set<Constraint*> &constraints,
        map<perm_string, SecType*> &initAssgns) {
        return _baseSolver->inferLabels(constraints, initAssgns);
    }

    /**
     * Returns all constraints of the form InputTypeVar <= SecType.
     * This is used as an assumption when typechecking the module, and then becomes a precondition for instantiation.
     * We can also omit any constraints that we can statically prove hold to simplify the generated z3.
     */
    virtual unordered_set<Constraint*> getInputConstraints(unordered_set<Constraint*> &constraints,
        std::map<perm_string, SecType*> &assignments) {
        unordered_set<Constraint*> result;
        //Extract constraints of the form: VarType(input) <= SecType
        //And resolves type variables based on result of inference
        for (auto c : constraints) {
            VarType* rhs = dynamic_cast<VarType*>(c->right);
            if (rhs && _inputNames.contains(rhs->get_type())) {
                SecType* resolvedType = c->left->substTypeVars(assignments, ConstType::TOP)->replaceConstTypes();
                if (!rhs->checkFlowsTo(resolvedType)) {
                    result.insert(new Constraint(resolvedType, rhs, c->pred));
                }
            }
        }
        return result;
    }

    /**
     * Given a set of type variable assignments (TypeVarName -> SecType)
     * and a set of target type variables, resolve assignments as much as possible
     * so that no type variables in the assignment.
     * E.g., if L(x) = L(y) and L(y) = TOP, then resolve L(x) = TOP
     * Then create constraints that imply these equalities (L(x) <= TOP, TOP <= L(x))
     */
    unordered_set<Constraint*> createOutputConstraints(map<perm_string, SecType*> &assignments) {
        unordered_set<Constraint*> result;
        //For the given set of variables, create constraints of the form
        //TypeVar(var) <= lbl_assigned_by_inferece
        //lbl_assigned_by_inferece <= TypeVar(var)
        //However, we use ConstType(inputname) to represent resolution of input type variables
        //These ConstTypes need to be replaced with TypeVar(inputname)
        for (auto name : _outputNames) {
            VarType* varTyp = new VarType(name);
            SecType* assignment;
            if (!assignments.contains(name)) {
                assignment = ConstType::BOT; //there must have been no constraints on this, assume it is BOT
            } else {
                 assignment = assignments[name]; 
            }
            //everything should be assigned, but if not set to TOP, and replace ConstType(x) with VarType(x)
            SecType* resolvedType = assignment->substTypeVars(assignments, ConstType::TOP)->replaceConstTypes(); 
            if (!varTyp->equals(resolvedType)) {
                Predicate* empty = new Predicate();
                Constraint* lConst = new Constraint(varTyp, resolvedType, empty);
                Constraint* rConst = new Constraint(resolvedType, varTyp, empty);
                result.insert(lConst);
                result.insert(rConst);
            } //otherwise we can skip since it is a tautology
        }
        return result;
    }

    void printOutputAssignments(map<perm_string, SecType*> &assignments, SexpPrinter &printer) {
        for (auto a : assignments) {
            if (_outputNames.contains(a.first)) {
                printer << a.first << " = ";
                auto tmp = a.second->substTypeVars(assignments, ConstType::TOP);
                tmp->dump(printer);
                printer.lineBreak();
            }
        }
    }
    virtual void setInputs(set<perm_string> inputNames) {
        _inputNames = inputNames; //just copy
    }
    virtual void clearInputs() {
        _inputNames.clear();
    }
    virtual void setOutputs(set<perm_string> outputNames) {
        _outputNames = outputNames; //just copy
    }
    virtual void clearoutputs() {
        _outputNames.clear();
    }
private:
    ConstraintSolver* _baseSolver;
    set<perm_string> _inputNames;
    set<perm_string> _outputNames;
};

//Returns true if success (type of ident matches target type or can be coerced)
//returns false otherwise.
//This will delete targetType if it does not save a reference to it
bool infer_baseType(BaseTypeMap &basetypes, PEIdent* ident, BaseType* targetType);

/**
 * This should remove any constraints that do not contain Type Variables
 * (VarType) anywhere in them.
 */
void removeConstantConstraints(unordered_set<Constraint*> &constraints);

/**
 * We want all constraints to be L <= R1 join R2 or L <= R
 * Therefore, any LHS that is the join type is converted into a list of new constraints
 * that replace the original.
 */
void canonicalizeConstraints(unordered_set<Constraint*> &constraints);

void deduplicate(unordered_set<Constraint*>&constraints);

void dumpAssignments(map<perm_string, SecType*> &assignments);

#endif