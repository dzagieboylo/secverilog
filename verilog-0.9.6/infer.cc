#include "infer.h"


//TODO make this unnecessary by getting rid of the pointers that are dangling everywhere!!!!!!!!
//And just make use of copy constructors to copy all of the predicates/hypotheses, etc.
//Then we can just use the fact that it is a set and the stdlib will do this for us on insertion
void deduplicate(unordered_set<Constraint*>&constraints) {
    unordered_set<Constraint*> result;
    for (auto c : constraints) {
        bool isDup = false;
        for (auto r : result) {
            if (c == r || *c == *r) {
                isDup = true;
            }
        }
        if (!isDup) {
            result.insert(c);
        }
    }
    constraints.clear();
    constraints.insert(result.begin(), result.end());
}

bool infer_baseType(BaseTypeMap &env, PEIdent* ident, BaseType* targetType) {
    bool result = false;
    bool usedTarget = false;
    if (ident && env.contains(ident->get_name())) {
        BaseType* curType = env[ident->get_name()];
        bool matches;
        if (targetType->isNextType() || targetType->isSeqType()) {
            matches = curType->isNextType() || curType->isSeqType();
        } else {
            matches = !(curType->isNextType() || curType->isSeqType());
        }
        if (matches) {
            result = true;
        } else if (!curType->isExplicit()) {
            //can coerce!
            cerr << "Coercing base type of " << ident->get_name() << " to " << targetType->name() << " from " << curType->name() << endl;
            env[ident->get_name()] = targetType;
            delete curType;
            assert(targetType->isExplicit()); //need to guarantee the type is not changed multiple times
            result = true;
            usedTarget = true;
        } else {
            //can't coerce - error!
            result = false;
        }
    } else {
        cerr << "Warning: tried to check base type of non PEIdent or missing base type" << endl;
        return true;
    }
    if (!usedTarget) {
        delete targetType;
    }
    return result;
}

void removeConstantConstraints(unordered_set<Constraint*> &constraints) {
    unordered_set<Constraint*> to_remove;
    for (auto c : constraints) {
        if (!c->left->hasTypeVar() && !c->right->hasTypeVar()) {
            to_remove.insert(c);
        }
    }
    for (auto rem : to_remove) {
        int removed = constraints.erase(rem);
        if (!removed) { cerr << "WARNING constraint " << rem << " was not removed" << endl;}
    }
}

void canonicalizeConstraints(unordered_set<Constraint*> &constraints) {
    unordered_set<Constraint*> to_remove;
    unordered_set<Constraint*> to_add;
    for (auto c : constraints) {
        MeetType* leftisMeet = dynamic_cast<MeetType*>(c->left);
        MeetType* rightisMeet = dynamic_cast<MeetType*>(c->right);
        if (leftisMeet || rightisMeet) {
            cerr << "WARN: found meet type when canonicalizing" << endl;
        }
        JoinType* rightIsJoin = dynamic_cast<JoinType*>(c->right);
        if (rightIsJoin) {
            to_remove.insert(c);
            unordered_set<Constraint*> newconsts;
            Constraint* left = new Constraint(c->left, rightIsJoin->getFirst(), c->pred);
            Constraint* right = new Constraint(c->left, rightIsJoin->getSecond(), c->pred);
            newconsts.insert(left);
            newconsts.insert(right);
            canonicalizeConstraints(newconsts);
            for (auto nc : newconsts) {
                to_add.insert(nc);
            }
            if (!to_add.contains(left)) {
                delete left;
            }
            if (!to_add.contains(right)) {
                delete right;
            }
            to_remove.insert(c);
        }
    }
    for (auto rem : to_remove) {
        constraints.erase(rem);
    }
    for (auto add : to_add) {
        constraints.insert(add);
    }
   deduplicate(constraints);
}

//Ensures that uninitialized type variables map to the given initialType
SecType* getTypeConstraint(perm_string name, std::map<perm_string, SecType*> &mapping, SecType* initialType) {
    if (mapping.contains(name)) {
        return mapping[name];
    } else {
        mapping[name] = initialType;
    }
    return mapping[name];
}

//Assert -> all constraints should be in the form R <= L where R is always a ConstType or a VarType
//(Other types not supported yet)
//This algorithm initializes all types to TOP (most restrictive label)
//If a constraint of the form VarType <= LBL is not satisfied, then VarType is set to Meet(VarType, LBL)
//If a constraint of any other form is not satisfied, then the constraints are NOT SAT
std::map<perm_string, SecType*> RestrictiveSolver::inferLabels(unordered_set<Constraint*> &constraints,map<perm_string, SecType*> &assignments) {
    size_t countSatisfied = 0;
    SecType* initType = ConstType::TOP;
    while (countSatisfied != constraints.size()) {
        countSatisfied = 0;
        for (auto c : constraints) {
            VarType* varrhs = dynamic_cast<VarType*>(c->right);
            auto rhsSub = c->right->substTypeVars(assignments, initType);
            auto lhsSub = c->left->substTypeVars(assignments, initType);
            bool satisfied = rhsSub->checkFlowsTo(lhsSub);
            if (!satisfied) {
                if (!varrhs) {
                    cerr << "Could not satisfy the following constraint:" << endl;
                    SexpPrinter debug(cerr, 80, 2, true);
                    c->right->dump(debug);
                    cerr << " flows to ";
                    c->left->dump(debug);
                    cerr << endl;
                    return assignments;
                } else {
                    //assign var to Meet(var assignment, lhs)
                    auto tmp = MeetType(getTypeConstraint(varrhs->get_type(), assignments, initType),c->left);
                    assignments[varrhs->get_type()] = tmp.simplify();
                }
            } else {
                countSatisfied += 1;
            }
        }
    }
    return assignments;
}

//Assert -> all constraints should be in the form R <= L where R is always a ConstType or a VarType
//(Other types not supported yet)
//This algorithm initializes all types to BOT (least restrictive label)
//If a constraint of the form VarType <= LBL is not satisfied, then VarType is set to Join(VarType, LBL)
std::map<perm_string, SecType*> PermissiveSolver::inferLabels(unordered_set<Constraint*> &constraints, map<perm_string, SecType*> &assignments) {
    size_t countSatisfied = 0;
    SecType* initType = ConstType::BOT;
    while (countSatisfied != constraints.size()) {
        countSatisfied = 0;
        for (auto c : constraints) {
            VarType* varlhs = dynamic_cast<VarType*>(c->left->simplify());
            auto rhsSub = c->right->substTypeVars(assignments, initType);
            auto lhsSub = c->left->substTypeVars(assignments, initType);
            bool satisfied = rhsSub->checkFlowsTo(lhsSub);
            if (!satisfied) {
                if (!varlhs) {
                    cerr << "Could not satisfy the following constraint:" << endl;
                    SexpPrinter debug(cerr, 80, 2, true);
                    c->right->dump(debug);
                    cerr << " flows to ";
                    c->left->dump(debug);
                    cerr << endl << "Constraints w/ type vars substituted: " << endl;
                    rhsSub->dump(debug) ;
                    cerr << " <= ";
                    lhsSub->dump(debug);
                    cerr << endl;
                    return assignments;
                } else {
                    //assign var to Join(var assignment, rhs)
                    auto tmp = JoinType(getTypeConstraint(varlhs->get_type(), assignments, initType),c->right);
                    assignments[varlhs->get_type()] = tmp.simplify();
                }
            } else {
                countSatisfied += 1;
            }
        }
    }
    return assignments;
}

//For the given set of variables, create constraints of the form
//TypeVar(var) <= lbl_assigned_by_inferece
//lbl_assigned_by_inferece <= TypeVar(var)
//However, we use ConstType(inputname) to represent resolution of input type variables
//These ConstTypes need to be replaced with TypeVar(inputname)
unordered_set<Constraint*> createResolvedConstraints(map<perm_string, SecType*> &assignments, set<perm_string> varNames) {
    unordered_set<Constraint*> result;
    for (auto name : varNames) {
        VarType* varTyp = new VarType(name);
        SecType* assignment = assignments[name]; //assume name is present in map
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

void dumpAssignments(map<perm_string, SecType*> &assignments) {
    SexpPrinter debug(cerr, 80, 2, true);
    for (auto a : assignments) {
        VarType* rhsType = dynamic_cast<VarType*>(a.second);
        debug << "Assigned " << a.first << " = ";
        a.second->dump(debug);
        while (rhsType) { //For convenience, dump the whole equality chain
            auto nextRhs = assignments[rhsType->get_type()];
            cerr << " = ";
            nextRhs->dump(debug);
            rhsType = dynamic_cast<VarType*>(nextRhs);
        }
        cerr << endl;
    }
}

//VarType substitution code

SecType* ConstType::replaceConstTypes() {
    return new VarType(name);
}
SecType* VarType::substTypeVars(map<perm_string, SecType*> &varMap, SecType* initType) {
    SecType* tmp = getTypeConstraint(varname_, varMap, initType);
    //May map to another type variable, and thus need to recursively substitute
    while (tmp->hasTypeVar()) {
        tmp = tmp->substTypeVars(varMap, initType);
    }
    return tmp;
}
SecType* JoinType::substTypeVars(map<perm_string, SecType*> &varMap, SecType* initType) {
    auto tmp = new JoinType(comp1_->substTypeVars(varMap, initType), comp2_->substTypeVars(varMap, initType));
    if (tmp->equals(this)){
        delete tmp;
        return this;
    } else {
        return tmp;
    }
}
SecType* JoinType::replaceConstTypes() {
    auto tmp = new JoinType(comp1_->replaceConstTypes(), comp2_->replaceConstTypes());
    if (tmp->equals(this)){
        delete tmp;
        return this;
    } else {
        return tmp;
    }
}
SecType* MeetType::substTypeVars(map<perm_string, SecType*> &varMap, SecType* initType) {
    auto tmp = new MeetType(comp1_->substTypeVars(varMap, initType), comp2_->substTypeVars(varMap, initType));
    if (tmp->equals(this)){
        delete tmp;
        return this;
    } else {
        return tmp;
    }
}
SecType* MeetType::replaceConstTypes() {
    auto tmp = new MeetType(comp1_->replaceConstTypes(), comp2_->replaceConstTypes());
    if (tmp->equals(this)){
        delete tmp;
        return this;
    } else {
        return tmp;
    }
}
SecType* QuantType::substTypeVars(map<perm_string, SecType*> &varMap, SecType* initType) {
    auto tmp = new QuantType(_index_var, _sectype->substTypeVars(varMap, initType));
    if (tmp->equals(this)){
        delete tmp;
        return this;
    } else {
        return tmp;
    }
}
SecType* QuantType::replaceConstTypes() {
    auto tmp = new QuantType(_index_var, _sectype->replaceConstTypes());
    if (tmp->equals(this)){
        delete tmp;
        return this;
    } else {
        return tmp;
    }
}
SecType* PolicyType::substTypeVars(map<perm_string, SecType*> &varMap, SecType* initType) {
    auto tmp = new PolicyType(_lower->substTypeVars(varMap, initType), _cond_name, _static,
     _dynamic, _upper->substTypeVars(varMap, initType));
    if (tmp->equals(this)){
        delete tmp;
        return this;
    } else {
        return tmp;
    }
}
SecType* PolicyType::replaceConstTypes() {
    auto tmp = new PolicyType(_lower->replaceConstTypes(), _cond_name, _static,
     _dynamic, _upper->replaceConstTypes());
    if (tmp->equals(this)){
        delete tmp;
        return this;
    } else {
        return tmp;
    }
}
//End VarType substitution