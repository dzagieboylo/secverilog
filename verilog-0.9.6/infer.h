#ifndef __Infer_H
#define __Infer_H

//These functions will do very basic inference of constant types for now.
#include "basetypes.h"
#include "sectypes.h"

//Returns true if success, else failure
bool infer_baseType(TypeEnv& env, PEIdent* ident, BaseType* targetType);
//Attempts to do a basic inference pass ONLY for implicitly assumed BOT types.
bool infer_secType(TypeEnv& env, PEIdent* ident, SecType* targetType);

#endif