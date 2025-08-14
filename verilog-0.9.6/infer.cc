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
        JoinType* leftIsJoin = dynamic_cast<JoinType*>(c->left);
        if (leftIsJoin) {
            cerr << "WARN: found join on left when canonicalizing" << endl;
        }
        if (rightIsJoin) {
            to_remove.insert(c);
            unordered_set<Constraint*> newconsts;
            for (auto comp : rightIsJoin->getComps()) {
                newconsts.insert(new Constraint(c->left->simplify(), comp, c->pred));
            }
            canonicalizeConstraints(newconsts);
            for (auto nc : newconsts) {
                to_add.insert(nc);
            }
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
            VarType* varrhs = dynamic_cast<VarType*>(c->right->simplify());
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
    SexpPrinter debug(cerr, 80, 2, true);
    while (countSatisfied != constraints.size()) {
        countSatisfied = 0;
        for (auto c : constraints) {
            VarType* varlhs = dynamic_cast<VarType*>(c->left);
            auto rhsSub = c->right->substTypeVars(assignments, initType)->simplify();
            auto lhsSub = c->left->substTypeVars(assignments, initType)->simplify();
            bool satisfied = rhsSub->checkFlowsTo(lhsSub);
            if (!satisfied) {
                if (!varlhs) {
                    cerr << "Could not satisfy the following constraint:" << endl;
                    c->right->dump(debug);
                    cerr << " flows to ";
                    c->left->dump(debug);
                    cerr << endl << "Constraints w/ type vars substituted: " << endl;
                    rhsSub->dump(debug) ;
                    cerr << " <= ";
                    lhsSub->dump(debug);
                    cerr << endl;
                    //Consider it satisfied, we will end up verifying satisfiability of all constraints again later anyway
                    //This makes debugging easier and allows us to imprecisely check flows to constraints during inference soundly
                    countSatisfied += 1;
                } else {
                    //assign var to Join(var assignment, rhs)
                    auto tmp = new JoinType(getTypeConstraint(varlhs->get_type(), assignments, initType),c->right);
                    assignments[varlhs->get_type()] = tmp->simplify();
                }
            } else {
                countSatisfied += 1;
            }
        }
    }
    return assignments;
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

//Begin VarType substitution code
SecType* ConstType::replaceConstTypes() {
    if (!isBottom() && !isTop()) { //these should stay consttypes
        return new VarType(name);
    } else {
        return this;
    }
}
SecType* canonicalizeSubstitution(VarType* v, SecType* lbl) {
    //If we have a variable mapping such as:
    // x => x JOIN y
    //Then we want to remove the "x maps to itself" with x => y
    //(this also applies to MEET)
    //for other types just leave it be for now.
    JoinType *isJoin     = dynamic_cast<JoinType *>(lbl);
    MeetType *right_meet     = dynamic_cast<MeetType *>(lbl);//TODO implement for meets
    if (isJoin) {
        isJoin->removeLbl(v);
    }
    return lbl;
}

SecType* VarType::substTypeVars(map<perm_string, SecType*> &varMap, SecType* initType) {
    SecType* tmp = getTypeConstraint(varname_, varMap, initType);
    //May map to another type variable, and thus need to recursively substitute
    //In recursive substitution map this to itself (which should otherwise never happen)
    //Then base case becomes tmp == this
    auto mapCopy(varMap);
    mapCopy[this->get_type()] = this;
    //If no initType is provided, then don't recurse (TODO do this cleaner)
    if (tmp->hasTypeVar() && initType && !tmp->equals(this)) {  
        tmp = tmp->substTypeVars(mapCopy, initType);
        //remove excess copies of this from tmp
        tmp = canonicalizeSubstitution(this, tmp);
    }
    return tmp;
}
SecType* JoinType::substTypeVars(map<perm_string, SecType*> &varMap, SecType* initType) {
    set<SecType*> newcomps;
    for (auto c : comps_) {
        newcomps.insert(c->substTypeVars(varMap, initType));
    }
    auto tmp = new JoinType(newcomps);
    if (tmp->equals(this)){
        delete tmp;
        return this;
    } else {
        return tmp;
    }
}
SecType* JoinType::replaceConstTypes() {
    set<SecType*> newcomps;
    for (auto c : comps_) {
        newcomps.insert(c->replaceConstTypes());
    }
    auto tmp = new JoinType(newcomps);
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