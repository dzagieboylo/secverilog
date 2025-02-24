#include "genvars.h"
#include "PExpr.h"
#include "StringHeap.h"
#include "sexp_printer.h"
#include <iterator>
#include <stdexcept>

/*
 * Add any genvars (which are used in generate blocks) that are used by
 * the given predicate into the result set.
 */
void collect_used_genvars(std::set<perm_string> &res, const Predicate &pred,
                          TypeEnv &env) {
  for (auto h : pred.hypotheses) {
    h->bexpr_->collect_used_genvars(res, env);
  }
}

/*
 * Add any genvars (which are used in generate blocks) that are used by
 * the given type into the result set.
 */
void collect_used_genvars(std::set<perm_string> &res, SecType *typ,
                          TypeEnv &env) {
  std::set<perm_string> depexp;
  typ->collect_dep_expr(depexp);
  for (auto i : depexp) {
    if (env.genVarVals.count(i)) {
      // it's a genvar!
      res.insert(i);
    }
  }
}
// for establish invariants only, not label checking
// this must be followed eventually by end_dump
void start_dump_genvar_quantifiers(SexpPrinter &printer,
                                   std::set<perm_string> &vars, TypeEnv &env) {
  if (vars.empty()) {
    return;
  }
  printer.startList("forall");
  printer.startList("");
  // declare all quantified variables
  for (auto g : vars) {
    printer.startList(g.str());
    printer << "Int";
    printer.endList();
  }
  printer.endList(); // end "" list
  printer.startList("=>");
  // declare all of their possible values
  for (auto g : vars) {
    // assume this exists and is non-empty, crashing otherwise is fine
    if (!env.genVarVals.count(g) || env.genVarVals[g].empty()) {
      std::cerr << "no genVarVals for " << g.str() << endl;
      throw "Missing genVarVals for genvar";
    }
    auto vals = env.genVarVals[g];
    printer.startList("or");
    for (auto v : vals) {
      printer.startList("=");
      printer << g.str();
      printer << std::to_string(v);
      printer.endList();
    }
    printer.endList(); // end or
  }
}

void end_dump_genvar_quantifiers(SexpPrinter &printer,
                                 std::set<perm_string> &vars) {
  if (vars.empty()) {
    return;
  }
  printer.endList(); // end =>
  printer.endList(); // end forall
}

// this function is used on the unassigned path check, as we want to be able to
// check if something is true under ANY of the generate values, as the all run.
void dump_genvar_every(SexpPrinter &printer, std::set<perm_string> &vars,
                       TypeEnv &env,
                       const std::function<void(SexpPrinter &)> &body) {
  if (vars.empty()) {
    body(printer);
    return;
  }

  if (vars.size() != 1) {
    throw std::runtime_error("cannot have multiple genvars on path! (sorry)");
  }

  printer.inList("forall", [&]() {
    printer.startList();
    // declare all quantified variables
    for (auto g : vars) {
      printer.inList(g.str(), [&]() { printer << "Int"; });
    }
    printer.endList();

    printer.inList("or", [&] {
      for (auto g : vars) {

        if (!env.genVarVals.count(g) || env.genVarVals[g].empty()) {
          std::cerr << "no genVarVals for " << g.str() << endl;
          throw "Missing genVarVals for genvar";
        }
        auto vals = env.genVarVals[g];
        for (auto v : vals) {
          printer.inList("=>", [&]() {
            printer.inList("=",
                           [&]() { printer << g.str() << std::to_string(v); });
            body(printer);
          });
        }
      }
    });
  });
}

void dump_genvar_pred(SexpPrinter &printer, std::set<perm_string> &vars,
                      TypeEnv &env) {
  if (vars.empty()) {
    return;
  }
  for (auto g : vars) {
    printer.startList("declare-fun");
    printer << g.str() << "()"
            << "Int";
    printer.endList();
    if (!env.genVarVals.count(g) || env.genVarVals[g].empty()) {
      std::cerr << "no genVarVals for " << g.str() << endl;
      throw "Missing genVarVals for genvar";
    }
    auto vals = env.genVarVals[g];
    printer.startList("assert");
    printer.startList("or");
    for (auto v : vals) {
      printer.startList("=");
      printer << g.str() << std::to_string(v);
      printer.endList();
    }
    printer.endList();
    printer.endList();
  }
}

void PGenerate::fill_genvar_vals(
    perm_string root, std::map<perm_string, std::list<int>> &gendefs) {
  // Check that the loop_index variable was declared in a
  // genvar statement.
  Design *des         = new Design;
  NetScope *container = des->make_root_scope(root);

  // setup output list
  std::list<int> genVals;
  //
  int genvar;
  probe_expr_width(des, container, loop_init);
  need_constant_expr = true;
  NetExpr *init_ex   = elab_and_eval(des, container, loop_init, -1);
  need_constant_expr = false;
  NetEConst *init    = dynamic_cast<NetEConst *>(init_ex);
  if (init == 0) {
    cerr << get_fileline() << ": error: Cannot evaluate genvar"
         << " init expression: " << *loop_init << endl;
    des->errors += 1;
    return;
  }
  genvar = init->value().as_long();
  delete init_ex;

  container->genvar_tmp     = loop_index;
  container->genvar_tmp_val = genvar;
  probe_expr_width(des, container, loop_test);
  need_constant_expr = true;
  NetExpr *test_ex   = elab_and_eval(des, container, loop_test, -1);
  need_constant_expr = false;
  NetEConst *test    = dynamic_cast<NetEConst *>(test_ex);
  if (test == 0) {
    cerr << get_fileline() << ": error: Cannot evaluate genvar"
         << " conditional expression: " << *loop_test << endl;
    des->errors += 1;
    return;
  }
  while (test->value().as_long()) {
    genVals.push_back(genvar); // insert genvar value for this iteration
    // Calculate the step for the loop variable.
    probe_expr_width(des, container, loop_step);
    need_constant_expr = true;
    NetExpr *step_ex   = elab_and_eval(des, container, loop_step, -1);
    need_constant_expr = false;
    NetEConst *step    = dynamic_cast<NetEConst *>(step_ex);
    if (step == 0) {
      des->errors += 1;
      return;
    }
    genvar                    = step->value().as_long();
    container->genvar_tmp_val = genvar;
    delete step;
    delete test_ex;
    probe_expr_width(des, container, loop_test);
    test_ex = elab_and_eval(des, container, loop_test, -1);
    test    = dynamic_cast<NetEConst *>(test_ex);
    assert(test);
  }
  gendefs[loop_index] = std::move(genVals);
  return;
}
