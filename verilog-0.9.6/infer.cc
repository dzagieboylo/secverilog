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

//Ensures that uninitialized type variables map to TOP
SecType* getTypeConstraint(perm_string name, std::map<perm_string, SecType*> &mapping) {
    if (mapping.contains(name)) {
        return mapping[name];
    } else {
        mapping[name] = ConstType::TOP;
    }
    return mapping[name];
}

//Assert -> all constraints should be in the form R <= L where R is always a ConstType or a VarType
//(Other types not supported yet)
std::map<perm_string, SecType*> inferLabels(unordered_set<Constraint*> &constraints) {
    std::map<perm_string, SecType*> assignments;
    size_t countSatisfied = 0;
    while (countSatisfied != constraints.size()) {
        countSatisfied = 0;
        for (auto c : constraints) {
            VarType* varrhs = dynamic_cast<VarType*>(c->right);
            auto rhsSub = c->right->substTypeVars(assignments);
            auto lhsSub = c->left->substTypeVars(assignments);
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
                    auto tmp = MeetType(getTypeConstraint(varrhs->get_type(), assignments),c->left);
                    assignments[varrhs->get_type()] = tmp.simplify();
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

//VarType substitution code

SecType* VarType::substTypeVars(map<perm_string, SecType*> &varMap) {
    SecType* tmp = getTypeConstraint(varname_, varMap);
    //May map to another type variable, and thus need to recursively substitute
    while (tmp->hasTypeVar()) {
        tmp = tmp->substTypeVars(varMap);
    }
    return tmp;
}
SecType* JoinType::substTypeVars(map<perm_string, SecType*> &varMap) {
    auto tmp = new JoinType(comp1_->substTypeVars(varMap), comp2_->substTypeVars(varMap));
    if (tmp->equals(this)){
        delete tmp;
        return this;
    } else {
        return tmp;
    }
}
SecType* MeetType::substTypeVars(map<perm_string, SecType*> &varMap) {
    auto tmp = new MeetType(comp1_->substTypeVars(varMap), comp2_->substTypeVars(varMap));
    if (tmp->equals(this)){
        delete tmp;
        return this;
    } else {
        return tmp;
    }
}
SecType* QuantType::substTypeVars(map<perm_string, SecType*> &varMap) {
    auto tmp = new QuantType(_index_var, _sectype->substTypeVars(varMap));
    if (tmp->equals(this)){
        delete tmp;
        return this;
    } else {
        return tmp;
    }
}
SecType* PolicyType::substTypeVars(map<perm_string, SecType*> &varMap) {
    auto tmp = new PolicyType(_lower->substTypeVars(varMap), _cond_name, _static,
     _dynamic, _upper->substTypeVars(varMap));
    if (tmp->equals(this)){
        delete tmp;
        return this;
    } else {
        return tmp;
    }
}

//End VarType substitution