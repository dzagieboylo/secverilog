#include "infer.h"

bool infer_baseType(TypeEnv &env, PEIdent* ident, BaseType* targetType) {
    bool result = false;
    bool usedTarget = false;
    if (ident && env.varsToBase.contains(ident->get_name())) {
        BaseType* curType = env.varsToBase[ident->get_name()];
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
            env.varsToBase[ident->get_name()] = targetType;
            delete curType;
            assert(targetType->isExplicit()); //need to guarantee the type is not changed multiple times
            result = true;
            usedTarget = true;
            //have to update seqvars if we added one
            if (targetType->isSeqType()) {
                env.seqVars.insert(ident->get_name());
            }
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

bool check_infer_secType(TypeEnv& env, PEIdent* ident, SecType* targetType) {
    return false;
}