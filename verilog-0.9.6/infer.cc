#include "infer.h"

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
            //have to update seqvars if we added one
            //TODO do this elsewhere
            // if (targetType->isSeqType()) {
            //     env.seqVars.insert(ident->get_name());
            // }
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

bool infer_secType(TypeEnv& env, PEIdent* ident, SecType* targetType) {
    SecType* curType = env.varsToType[ident->get_name()];
    if (curType->isExplicit() || !curType->isBottom()) {
        return false; //not modified if already modified or not BOT type
    }
    SecType* join = new JoinType(curType, targetType, true); //don't allow more updating (for now)
    SecType* newType =join->simplify();
    delete join;
    env.varsToType[ident->get_name()] = newType;
    return true;
}

void collect_type_constraints(map<perm_string, Module *> modules,
 map<perm_string, BaseTypeMap*> & baseTypes, map<perm_string, SecTypeMap*> &secTypes,
 map<perm_string, set<Constraint*>*> &consts) {
    for (auto entry : modules) {
        auto name = entry.first;
        auto module = entry.second;
        
        auto modConsts = new set<Constraint*>();
        consts[name] = modConsts;

        //Ignore all of these things for now, providing a warning if you find any:
        //parameters, localparams, genvars, specparams, defparams, events
        if (!module->parameters.empty()) {
            cerr << "Found module parameters! Skipping type constraint collection." << endl;
        }
        if (!module->localparams.empty()) {
            cerr << "Found module localparams! Skipping type constraint collection." << endl;
        }
        if (!module->genvars.empty()) {
            cerr << "Found module genvars! Skipping type constraint collection." << endl;
        }
        if (!module->specparams.empty()) {
            cerr << "Found module localparams! Skipping type constraint collection." << endl;
        }
        if (!module->defparms.empty()) {
            cerr << "Found module localparams! Skipping type constraint collection." << endl;
        }
        if (!module->events.empty()) {
            cerr << "Found module events! Skipping type constraint collection." << endl;
        }
        if (!module->analog_behaviors.empty()) {
            throw "Analog behaviors not supported";
        }
        if (!module->specify_paths.empty()) {
            throw "Specify paths not supported";
        }

        for (auto gate : module->get_gates()) {
            PGAssign *assign = dynamic_cast<PGAssign *>(gate);
            PGModule *modinst = dynamic_cast<PGModule *>(gate);
            if (modinst) {
                auto instantiated = modules.find(modinst->get_type());
                if (instantiated != modules.end()) {
                    //modinst->get_name(); N.B. This is the instantiated variable's name (as opposed to the module's type)
                    SecTypeMap* callerTypes = secTypes[name];
                    SecTypeMap* calleeTypes = secTypes[instantiated->first];
                    collect_type_constraints(modinst, *modConsts,
                        instantiated->first, instantiated->second, *calleeTypes, *callerTypes);
                } else {
                    throw "Module definition not found!";
                }
            } else if (assign) {
                collect_type_constraints(assign, *modConsts);
            } else {
                cerr << "Found unexpected PGate type! " << endl;
            }
        }
        for (auto process : module->behaviors) {
            collect_type_constraints(process, *modConsts);
        }
    }
   
}

void collect_type_constraints(PGAssign* assign, set<Constraint*>& consts) {
    auto left = assign->pin(0);
    auto right = assign->pin(1);
}

void collect_type_constraints(PGModule* mod, set<Constraint*>& consts, perm_string name,
 Module* moddef, SecTypeMap &modTypes, SecTypeMap &topLevelTypes) {
    perm_string inst_name = mod->get_name();
    auto wires = moddef->wires;
    for (unsigned idx = 0; idx < mod->get_pin_count(); idx += 1) {
        auto pin = wires.find(mod->get_pin_name(idx));
        if (pin != wires.end()) {
            PWire *port = pin->second;
            auto port_type = port->get_port_type();
            //TODO for now, don't do polymorphism -> all instances of module must use same labels
            //Later, we can instantiate separate type variables for each instance by disambiguating their names
            auto port_sec_type = modTypes[mod->get_pin_name(idx)];
            auto param_sec_type = topLevelTypes[mod->get_param(idx)->get_name()];
            if (port_type == NetNet::PINPUT) {
                //Flows to input
                consts.insert(new Constraint(port_sec_type, param_sec_type, NULL, NULL));
            } else if (port_type == NetNet::PINOUT) {
                //Equal
                consts.insert(new Constraint(port_sec_type, param_sec_type, NULL, NULL));
                consts.insert(new Constraint(param_sec_type, port_sec_type, NULL, NULL));
            } else {
                //POUTPUT
                //Flows from output
                consts.insert(new Constraint(param_sec_type, port_sec_type, NULL, NULL));
            }
        }
    }
    //Constraint -> for each k,v in PinMap: v < = k
    //Constraint -> for each k,v in ParamMap: 
}
void collect_type_constraints(PProcess* assign, set<Constraint*>& consts) {}


/**
 * Generate assignment typing constraints (either noblocking or blocking).
 */
void collect_assignment_constraint(PExpr *lhs, PExpr *rhs, bool is_blocking, BaseTypeMap baseTypes,
                          set<perm_string> &defAssgns, set<Constraint*> consts) {
  // when the RHS is a PETernary expression, i.e. e1?e2:e3, we first
  // translate to the equivalent statements
  PETernary *ternary = dynamic_cast<PETernary *>(rhs);
  if (ternary == NULL) {
    SecType *ltype, *rtype, *ltype_orig;
    BaseType *lbase;
    PEIdent *lident = dynamic_cast<PEIdent *>(lhs);
    lbase           = lhs->check_base_type(baseTypes);
    if (lident != NULL) {
      // if lhs is v[x], only want to put type(v) in the type
      ltype_orig = lident->typecheckName(env, false);
      // want next cycle version if is NextType
      ltype = lident->typecheckName(env, lbase->isNextType());
    } else {
      auto msg = new std::string("Assigned to non identifier on LHS: ");
      *msg += lhs->get_name().str();
      throw std::runtime_error(*msg);
    }

    rtype = new JoinType(rhs->typecheck(env), env.pc);
    // if lhs is v[x], want to include type(x) in the rhs type
    rtype = new JoinType(rtype, lident->typecheckIdx(env));
    // if lhs is NOT a quant type and this is an indexed expression
    // (i.e., we are only assigning to part of the variable)
    // then add ltype_orig into rtype
    if (!dynamic_cast<QuantType *>(ltype_orig) && lident->hasIndexExpr()) {
      rtype = new JoinType(rtype, ltype_orig);
    }
    // is com type and has reflexive label
    bool isRecursiveCom =
        !lbase->isNextType() && ltype->hasExpr(lhs->get_name());
    if (isRecursiveCom && is_blocking) {
        //For now, don't support this
        cerr << "Warning! Recursive Combinational Labels not supported with constraint inference yet." << endl;
    } else {
      // is seq type or non rec dep com
      typecheck_assignment_constraint(printer, ltype, rtype, precond, note,
                                      NULL, env);
      // need no-sensitive-upgrade check when:
      //   - lident has a recursive dep type
      //   - lident is not definitely assigned
      //   - lident is a NEXT type (i.e., it's a register assignment)
      if (!defAssgns.contains(lhs->get_name()) &&
          (ltype_orig->isDepType() && lbase->isNextType())) {
        PEIdent *origName = lident->get_this_cycle_name();
        // is recursive if ltype contains lident
        if (ltype_orig->hasExpr(origName->get_name())) {
          // either  isDefAssigned(lident) OR forall contexts.
          //  (leq pc ltype_orig)
          //  rtype also flows to cur cycle label of lident in any context
          string newNote = note + "--No-sensitive-upgrade-check;";
          typecheck_assignment_constraint(printer, ltype_orig, env.pc, precond,
                                          newNote, origName, env);
        }
      }
    }
  } else {
    auto tmp = ternary->translate(lhs, is_blocking);
    tmp->typecheck(printer, env, precond, defAssgns);
    delete tmp;
  }
}

SecType* generate_rhs_type(PExpr* rhs) {
    return NULL;
}

SecType* generate_lhs_type(PExpr* lhs) {
    return NULL;
}