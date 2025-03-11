#ifndef __TYPECHECK_H_
#define __TYPECHECK_H_


#include "PExpr.h"
#include "StringHeap.h"
#include "config.h"
#include "PEvent.h"
#include "PGate.h"
#include "PGenerate.h"
#include "PSpec.h"
#include "compiler.h"
#include "genvars.h"
#include "infer.h"
#include "ivl_assert.h"
#include "netlist.h"
#include "netmisc.h"
#include "parse_api.h"
#include "parse_misc.h"
#include "path_assign.h"
#include "pform.h"
#include "sectypes.h"
#include "sexp_printer.h"
#include "util.h"
#include <algorithm>
#include <cstdlib>
#include <fstream>
#include <ranges>
#include <regex>
#include <sstream>
#include <stdexcept>
#include <type_traits>
#include <typeinfo>

#define ASSUME_NAME "assume"


void output_type_families(SexpPrinter &printer, char *depfun);
void output_lattice(SexpPrinter &out, char *lattice);

void printDecl(SexpPrinter &out, const char *expr) {
  out.startList("declare-fun");
  out << expr << "()"
      << "Int";
  out.endList();
}
void printBounds(SexpPrinter &out, const char *expr, PWire *def) {
  if (def) {
    out.startList("assert");
    out.startList("<=");
    out << "0" << expr;
    out.endList();
    out.endList();

    out.startList("assert");
    out.startList("<=");
    out << expr << std::to_string((1 << (def->getRange() + 1)) - 1);
    out.endList();
    out.endList();
  }
}

void printDeclaration(SexpPrinter &out, const char *expr, PWire *def) {
  printDecl(out, expr);
  printBounds(out, expr, def);
}

struct root_elem {
  Module *mod;
  NetScope *scope;
};

// TODO C++26 should introduce std::embed
const char *default_lattice =
#include "default_lattice.lat"
    ;

/**
 * SecVerilog by default declares a minimal lattice with only bottom and top:
 *                   HIGH
 *
 *                   LOW
 *
 * Programmers can define their own lattice structure in a Z3 file,
 * by using the [-l lattice_file] option to SecVerilog. This will not
 * overwrite the existing bottom and top, and can only specify other, new
 * elements.
 */
void output_lattice(SexpPrinter &out, char *lattice) {
  out.lineBreak();
  out.writeRawLine(default_lattice);

  // append the user-defined lattice
  if (lattice) {
    out.lineBreak();
    string line;
    ifstream infile(lattice);
    while (getline(infile, line)) {
      out.writeRawLine(line);
    }
  }
}

/**
 * SecVerilog by default declares a simple type-level function "LH",
 * which maps 0 to LOW and 1 to HIGH.
 *
 * Programmers can define their own function in a Z3 file,
 * using the [-F depfun_file] option to SecVerilog.
 */
void output_type_families(SexpPrinter &printer, char *depfun) {
  printer.lineBreak();
  printer.addComment("function that maps 0 to LOW; 1 to HIGH");
  printer.singleton("declare-fun LH (Int) Label");
  printer.singleton("assert (= (LH 0) LOW)");
  printer.singleton("assert (= (LH 1) HIGH)");

  // append the user-defined type-level functions
  if (depfun) {
    string line;
    ifstream infile(depfun);
    while (getline(infile, line)) {
      printer.writeRawLine(line);
    }
  }
}

void collectBaseTypes(map<perm_string, Module *> modules, map<perm_string, BaseTypeMap>&basetypes) {
  for (auto m : modules) {
    auto name = m.first;
    BaseTypeMap curMap;
    for (auto w : m.second->wires) {
      auto wirename = w.second->basename();
      curMap[wirename] = w.second->get_base_type();
    }
    basetypes[name] = curMap;
  }
}

void collectSecTypes(map<perm_string, Module *> modules, map<perm_string, SecTypeMap>&sectypes) {
  for (auto m : modules) {
    auto name = m.first;
    SecTypeMap curMap;
    for (auto w : m.second->wires) {
      auto wirename = w.second->basename();
      //make sure vartypes are unique per module
      auto varTypeName = prepend_perm_string(name, wirename);
      auto sectype = w.second->get_sec_type();
      if (sectype == NULL) {
        cerr << "WARN: Found NULL sectype for " << wirename.str() << ", will attempt to infer" << endl;
        auto tmp = new VarType(varTypeName);
        w.second->set_sec_type(tmp);
      }
      curMap[wirename] = w.second->get_sec_type();
    }
    sectypes[name] = curMap;
  }
}

std::set<VarType*> collectVarTypes(map<perm_string, Module *> modules, SecTypeMap &types, Module *mod) {
  set<VarType*> result;
  set<perm_string> names;
  for (auto v : types) {
    auto typ = v.second;
    VarType* vartyp = dynamic_cast<VarType*>(typ);
    if (vartyp && !names.contains(vartyp->get_type())) {
      names.insert(vartyp->get_type());
      result.insert(vartyp);
    }
  }
  for (auto gate : mod->get_gates()) {
    PGModule *pgmodule = dynamic_cast<PGModule *>(gate);
    // make sure the parameters have the same label as module declaration
    if (pgmodule != NULL) {
      auto moddef = modules[pgmodule->get_type()];
      auto modwires = moddef->wires;
      for (unsigned idx = 0; idx < pgmodule->get_pin_count(); idx += 1) {
        auto port = modwires[pgmodule->get_pin_name(idx)];
        SecType* portType = port->get_sec_type();
        VarType* vartyp = dynamic_cast<VarType*>(portType);
        if (vartyp && !names.contains(vartyp->get_type())) {
          names.insert(vartyp->get_type());
          result.insert(vartyp);
        }
      }
    }
  }
  return result;
}
ofstream createOutputFile(perm_string name, string ext, bool append) {
  ofstream z3file;
  string z3filename = string(name.str());
  size_t pos        = z3filename.find_first_of('.');
  if (pos != string::npos) {
    z3filename = z3filename.substr(0, pos);
  }
  std::ios_base::openmode mode = append ? std::ios_base::app : std::ios_base::out;
  z3file.open((z3filename + ext).c_str(), mode);  
  return z3file;
}

#endif