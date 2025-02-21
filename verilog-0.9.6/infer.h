#ifndef __Infer_H
#define __Infer_H

//These functions will do very basic inference of constant types for now.
#include "basetypes.h"
#include "parse_misc.h"
#include "sectypes.h"
#include "Module.h"
#include "PGate.h"
#include "PWire.h"

//Returns true if success (type of ident matches target type or can be coerced)
//returns false otherwise.
//This will delete targetType if it does not save a reference to it
bool infer_baseType(BaseTypeMap &basetypes, PEIdent* ident, BaseType* targetType);
//Attempts to do a basic inference pass for non-explicit security types.
//TODO allow multiple inference passes (i.e., re-assigning a variable multiple times)
//Returns true if modified, false otherwise
bool infer_secType(TypeEnv& env, PEIdent* ident, SecType* targetType);

//Collects all constraints between types.
//Module instantiations are covariant in their inputs,
//Contra-variant in their outputs,
//and invariant in their in-outs.
void collect_type_constraints(map<perm_string, Module *> modules,
 map<perm_string, BaseTypeMap*> & baseTypes, map<perm_string, SecTypeMap*> &secTypes,
 map<perm_string, set<Constraint*>*> &consts);
void collect_type_constraints(PGAssign* assign, set<Constraint*>& consts);
void collect_type_constraints(PGModule* mod, set<Constraint*>& consts, perm_string name,
 Module* moddef, SecTypeMap &modTypes, SecTypeMap &topLevelTypes);
void collect_type_constraints(PProcess* assign, set<Constraint*>& consts);
#endif