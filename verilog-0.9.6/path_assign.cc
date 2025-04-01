#include "path_assign.h"
#include "Module.h"
#include "PExpr.h"
#include "PGenerate.h"
#include "Statement.h"
#include "StringHeap.h"
#include "compiler.h"
#include "genvars.h"
#include "ivl_target.h"
#include "pform_types.h"
#include "sectypes.h"
#include "sexp_printer.h"
#include <ranges>
#include <sstream>
#include <stdexcept>
#include <vector>

static inline void collectPathsBehavior(PathAnalysis &p, PProcess &b,
                                        TypeEnv &env,
                                        const std::set<perm_string> &genvars) {
  if (b.type() != IVL_PR_INITIAL) {
    Predicate emptyPred;
    emptyPred.hypotheses.insert(new Hypothesis(new PEBoolean(true)));
    b.statement()->collect_assign_paths(p, env, emptyPred, genvars);
  }
}

static inline void collectPathsGenerate(PathAnalysis &p, const PGenerate &gen,
                                        TypeEnv &env,
                                        const std::set<perm_string> &genvars) {
  auto copy = genvars;
  copy.insert(gen.loop_index);
  for (auto g : gen.generate_schemes)
    collectPathsGenerate(p, *g, env, copy);
  for (auto b : gen.behaviors)
    collectPathsBehavior(p, *b, env, copy);
}

PathAnalysis get_paths(Module &m, TypeEnv &env) {
  PathAnalysis paths;
  std::set<perm_string> empty_genvars;
  for (auto g : m.generate_schemes)
    collectPathsGenerate(paths, *g, env, empty_genvars);
  for (auto b : m.behaviors)
    collectPathsBehavior(paths, *b, env, empty_genvars);

  // debug printing of paths
  if (debug_typecheck)
    for (auto &p : paths) {
      std::cerr << p.first << ":\n";
      std::cerr << p.second.size() << "\n";
      for (auto &pred : p.second) {
        std::cerr << pred.path;
      }
    }
  return paths;
}

void dump_is_def_assign(SexpPrinter &p, PathAnalysis &path_analysis,
                        const PEIdent &varname, TypeEnv &env) {

  if (!path_analysis.contains(varname) || path_analysis[varname].empty()) {
    p << "false";
    return;
  }
  dump_on_paths(p, path_analysis[varname], env);
}

/**
 * when @param ident is null, the left side of the pairs in the return will be
 * as well
 */
std::vector<std::pair<PEIdent *, Predicate>>
expand_genvars(PEIdent *ident, const AssignmentPath &path, TypeEnv &env) {
  std::vector<std::pair<PEIdent *, AssignmentPath>> worklist = {
      std::make_pair(ident, path)};
  std::vector<std::pair<PEIdent *, Predicate>> ret;

  if (debug_typecheck) {
    cerr << "expanding genvars in " << ident << endl;
  }

  while (!worklist.empty()) {
    auto [next_id, next_path] = worklist.back();
    worklist.pop_back();

    if (next_path.genvars.empty()) {
      ret.emplace_back(next_id, next_path.path);
    } else {
      auto genvars      = next_path.genvars;
      auto first_genvar = genvars.extract(genvars.begin()).value();

      for (auto val : env.genVarVals[first_genvar]) {
        auto val_str = lex_strings.make(std::to_string(val).c_str());
        std::map<perm_string, perm_string> map{{first_genvar, val_str}};
        auto subst_path = *next_path.path.subst(map);
        auto subst_ident =
            next_id ? (dynamic_cast<PEIdent *>(next_id->subst(map))) : 0;
        AssignmentPath new_assign_path = {subst_path, genvars};
        worklist.emplace_back(subst_ident, new_assign_path);
      }
    }
  }

  return ret;
}

std::vector<std::pair<PEIdent, AssignmentPath>>
all_paths_arr(const perm_string base_name, const PathAnalysis &all_paths) {
  std::vector<std::pair<PEIdent, AssignmentPath>> ret;

  for (auto &[id, paths] : all_paths) {
    if (id.get_name() == base_name)
      for (auto path : paths) {
        ret.emplace_back(id, path);
      }
  }
  return ret;
}

void dump_isnt_assigned_normal(SexpPrinter &p, const perm_string base_name,
                               TypeEnv &env) {
  auto paths = all_paths_arr(base_name, env.analysis);

  auto exp_paths = std::ranges::transform_view(paths,
                                               [&env](auto &pr) {
                                                 return expand_genvars(
                                                     nullptr, pr.second, env);
                                               }) |
                   std::views::join;

  p.inList("not", [&]() {
    p.inList("or", [&]() {
      if (exp_paths.begin() == exp_paths.end()) {
        p << "false";
      }
      for (auto &[_, path] : exp_paths) {
        p << path;
      }
    });
  });
}

void dump_isnt_assigned_array(SexpPrinter &p, const perm_string base_name,
                              int idx, TypeEnv &env) {
  auto paths = all_paths_arr(base_name, env.analysis);

  auto exp_paths = std::ranges::transform_view(paths,
                                               [&env](auto &pr) {
                                                 return expand_genvars(
                                                     &pr.first, pr.second, env);
                                               }) |
                   std::views::join | std::views::filter([idx](auto &pair) {
                     auto id = pair.first;

                     std::stringstream ss;
                     ss << id->path().back().index.front(); // lol

                     std::string str = ss.str().substr(1, ss.str().size() - 2);

                     if (std::all_of(CONST_IT(str),
                                     [](char c) { return std::isdigit(c); })) {
                       auto parsed = std::stoi(str);
                       return parsed == idx;
                     } else {
                       return true;
                     }
                   });

  p.inList("not", [&]() {
    p.inList("or", [&]() {
      if (exp_paths.begin() == exp_paths.end()) {
        p << "false";
      }
      for (auto &[id, path] : exp_paths) {
        std::stringstream ss;
        ss << id->path().back().index.front();

        auto idx_str = ss.str().substr(1, ss.str().size() - 2);

        p.inList("and", [&]() {
          p.inList("=", [&]() { p << std::to_string(idx) << idx_str; });
          p << path;
        });
      }
    });
  });
}

void dump_on_paths(SexpPrinter &p, const std::vector<AssignmentPath> &paths,
                   TypeEnv &env) {

  std::set<perm_string> genvars;
  for (auto &path : paths) {
    genvars.insert(CONST_IT(path.genvars));
  }

  dump_genvar_every(p, genvars, env, [&](SexpPrinter &printer) {
    printer.inList("or", [&]() {
      std::for_each(paths.begin(), paths.end(),
                    [&printer](auto &path) { printer << path.path; });
    });
  });
}

void dump_no_overlap_anal(SexpPrinter &p, Module &m, TypeEnv &env,
                          set<perm_string> &vars) {
  p.inList("echo", [&]() { p.printAtom("\"Starting assigned-once checks\""); });

  for (auto v : vars) {
    auto paths     = all_paths_arr(v, env.analysis);
    auto exp_paths = std::ranges::transform_view(
                         paths,
                         [&env](auto &pr) {
                           return expand_genvars(&pr.first, pr.second, env);
                         }) |
                     std::views::join;

    std::vector<Predicate> all_paths;
    for (auto &[_, path] : exp_paths) {
      all_paths.push_back(path);
    }
    p.singleton("push");
    p.inList("echo", [&]() {
      p << std::string("\"Assigned once for: ") + v.str() + "\"";
    });
    p.inList("assert", [&]() {
      p.inList("or", [&]() {
        if (all_paths.size() <= 1)
          p << "false";

        for (auto i = all_paths.begin(); i != all_paths.end(); ++i) {
          for (auto j = i + 1; j != all_paths.end(); ++j) {
            p.inList("and", [&]() { p << *i << *j; });
          }
          p << "true";
        }
      });
    });
    p.singleton("check-sat");
    p.singleton("pop");
    p.lineBreak();
  }

  // auto isDepVar =
  //     [&vars](const std::pair<PEIdent, std::vector<AssignmentPath>> &pred) {
  //       return vars.contains(pred.first.get_name());
  //     };
  // for (auto &[var, paths] : std::ranges::filter_view(env.analysis, isDepVar))
  // {

  // }
  // {
  //   std::set<perm_string> genvar_idx_used;

  //   // for (auto &[var, paths] : path_analysis) {

  //   p.singleton("push");

  //     p.inList("assert", [&]() {
  //     start_dump_genvar_quantifiers(p, genvar_idx_used, env);

  //     p.inList("or", [&]() {
  //       if (paths.size() <= 1)
  //         p.printAtom("false");
  //       for (auto i = paths.cbegin(); i != paths.cend(); ++i) {
  //         for (auto j = i + 1; j != paths.cend(); ++j) {
  //           p.inList("and", [&]() { p << *i << *j; });
  //         }
  //       }
  //     });
  //     end_dump_genvar_quantifiers(p, genvar_idx_used);
  //   });
  //   std::string msg = std::string("\"checking paths of ") + var.str() +
  //   "\""; p.inList("echo", [&]() { p.printAtom(msg); });
  //   p.singleton("check-sat");
  //   p.singleton("pop");
  // }
  // p.inList("echo", [&]() { p.printAtom("\"Ending assigned-once
  // checks\"");
  // });
}

bool isDefinitelyAssigned(PEIdent *varname, PathAnalysis &paths) {
  throw new std::runtime_error("Unimplemented");
}

void collect_assign_path_id(PExpr* expr, PathAnalysis &paths, TypeEnv &env,
                                    Predicate &pred,
                                    const std::set<perm_string> &genvars) {
  auto lv = dynamic_cast<PEIdent *>(expr);
  auto lvconcat = dynamic_cast<PEConcat*>(expr);
  if (lv != nullptr) {
    paths[*lv].push_back({pred, genvars});
  }
  if (lvconcat != nullptr) {
    auto params = lvconcat->getParams();
    for (unsigned int i = 0; i < params.count(); i++) {
      collect_assign_path_id(params[i], paths, env, pred, genvars);
    }
  }
  if (lv == nullptr && lvconcat == nullptr) {
    expr->dump(cerr);
    throw new std::runtime_error("non PEIdent on lhs!");
  } 
}

void Statement::collect_assign_paths(PathAnalysis &, TypeEnv &, Predicate &,
                                     const std::set<perm_string> &genvars) {}

void PAssign_::collect_assign_paths(PathAnalysis &paths, TypeEnv &env,
                                    Predicate &pred,
                                    const std::set<perm_string> &genvars) {
  collect_assign_path_id(lval_, paths, env, pred, genvars);
}

void PBlock::collect_assign_paths(PathAnalysis &paths, TypeEnv &env,
                                  Predicate &pred,
                                  const std::set<perm_string> &genvars) {
  for (uint i = 0; i < list_.count(); ++i)
    list_[i]->collect_assign_paths(paths, env, pred, genvars);
}

void PCAssign::collect_assign_paths(PathAnalysis &paths, TypeEnv &env,
                                    Predicate &pred,
                                    const std::set<perm_string> &genvars) {
  auto lv = dynamic_cast<PEIdent *>(lval_);
  if (lv == nullptr) {
    lval_->dump(cerr);
    throw new std::runtime_error("non PEIdent on lhs!");
  }
  paths[*lv].push_back({pred, genvars});
}

void PCondit::collect_assign_paths(PathAnalysis &paths, TypeEnv &env,
                                   Predicate &pred,
                                   const std::set<perm_string> &genvars) {
  auto oldPred = pred;
  if (if_ != NULL) {
    absintp(pred, env, true, true);
    if_->collect_assign_paths(paths, env, pred, genvars);
    pred.hypotheses = oldPred.hypotheses;
  }
  if (else_ != NULL) {
    absintp(pred, env, false, true);
    else_->collect_assign_paths(paths, env, pred, genvars);
    pred.hypotheses = oldPred.hypotheses;
  }
}

void PForStatement::collect_assign_paths(PathAnalysis &paths, TypeEnv &env,
                                         Predicate &pred,
                                         const std::set<perm_string> &genvars) {
  // auto oldPred = pred;
  // if (statement_) {
  //   absintp(pred, env);
  //   statement_->collect_assign_paths(paths, env, pred);
  //   pred.hypotheses = oldPred.hypotheses;
  // }
  cerr << "warning! for statement not counted for unassigned paths. (don't "
          "put "
          "seq types here!)"
       << endl;
}

void PEventStatement::collect_assign_paths(
    PathAnalysis &paths, TypeEnv &env, Predicate &pred,
    const std::set<perm_string> &genvars) {
  statement_->collect_assign_paths(paths, env, pred, genvars);
}
