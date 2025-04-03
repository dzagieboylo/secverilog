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
    virtual map<perm_string, SecType*> inferLabels(unordered_set<Constraint*> &constraints) = 0;
};

class RestrictiveSolver : ConstraintSolver {
public:
    RestrictiveSolver() {}
    virtual ~RestrictiveSolver() {}
    /**
     * Use the iterative algorithm from the decentralized label paper to
     * infer assignments from type variables to labels.
    */
    virtual map<perm_string, SecType*> inferLabels(unordered_set<Constraint*> &constraints);
};

class PermissiveSolver : ConstraintSolver {
public:
    PermissiveSolver() {}
    virtual ~PermissiveSolver() {}
    /**
     * Use the iterative algorithm from the Viadcut paper
     * infer assignments from type variables to labels.
     */
    virtual map<perm_string, SecType*> inferLabels(unordered_set<Constraint*> &constraints);
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

//TODO: 
/**
 * We want all constraints to be L <= R1 join R2 or L <= R
 * Therefore, any LHS that is the join type is converted into a list of new constraints
 * that replace the original.
 */
void canonicalizeConstraints(unordered_set<Constraint*> &constraints);

void deduplicate(unordered_set<Constraint*>&constraints);


void dumpAssignments(map<perm_string, SecType*> &assignments);

#endif