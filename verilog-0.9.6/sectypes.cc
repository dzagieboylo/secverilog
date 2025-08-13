/*
 * Copyright (c) 1998-2013 Danfeng Zhang (zhangdf@cs.cornell.edu)
 *
 *    This source code is free software; you can redistribute it
 *    and/or modify it in source code form under the terms of the GNU
 *    General Public License as published by the Free Software
 *    Foundation; either version 2 of the License, or (at your option)
 *    any later version.
 *
 *    This program is distributed in the hope that it will be useful,
 *    but WITHOUT ANY WARRANTY; without even the implied warranty of
 *    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *    GNU General Public License for more details.
 *
 *    You should have received a copy of the GNU General Public License
 *    along with this program; if not, write to the Free Software
 *    Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA 02111-1307, USA
 */

/*
 * The netlist types, as described in this header file, are intended
 * to be the output from elaboration of the source design. The design
 * can be passed around in this form to the various stages and design
 * processors.
 */
#include "sectypes.h"
#include "PExpr.h"
#include "StringHeap.h"
#include "genvars.h"
#include <algorithm>
#include <iterator>
#include <sstream>
#include <string>
#include <variant>

extern perm_string nextify_perm_string(perm_string s);

void dumpZ3Func(SexpPrinter &printer, perm_string name, list<str_or_num> args) {
  printer.startList(name.str());
  for (auto pstr : args)
    printer << std::visit(str_or_num_to_string(), pstr);
  printer.endList();
}

ConstType *ConstType::TOP = new ConstType(lex_strings.make("HIGH"), true);
ConstType *ConstType::BOT = new ConstType(lex_strings.make("LOW"), true);

ConstType::ConstType(bool isExplicit) {
  name = lex_strings.make("LOW");
  _isExplicit = isExplicit;
}

ConstType::ConstType(perm_string n, bool isExplicit) {
  // currently, only support Low and High
  if (n == "Low" || n == "L")
    name = lex_strings.make("LOW");
  else if (n == "High" || n == "H")
    name = lex_strings.make("HIGH");
  else {
    name = n;
  }
  _isExplicit = isExplicit;
}

ConstType::~ConstType() {}

bool ConstType::equals(SecType *st) {
  ConstType *ct = dynamic_cast<ConstType *>(st);
  if (ct != NULL) {
    return name == ct->name;
  }
  return false;
}

//Assumes that only bottom and top exist in the lattice
//Conservatively overapproximates the flows to relation statically
bool SecType::checkFlowsTo(SecType* other) {
  ConstType *right_const   = dynamic_cast<ConstType*>(other);
  VarType *right_var       = dynamic_cast<VarType*>(other);
  JoinType *right_join     = dynamic_cast<JoinType *>(other);
  MeetType *right_meet     = dynamic_cast<MeetType *>(other);
  QuantType *right_quant   = dynamic_cast<QuantType *>(other);
  IndexType *right_index   = dynamic_cast<IndexType *>(other);
  PolicyType *right_policy = dynamic_cast<PolicyType *>(other);
  if (isBottom() || other->isTop()) {
    return true;
  } else if (this->equals(other)) {
    return true;
  } else if (right_const) {
    return right_const->equals(this);
  } else if (right_join) {
    for (auto c : right_join->getComps()) {
      if (this->checkFlowsTo(c)) {
        return true;
      }
    }
    return false;
  } else if (right_meet) {
    return this->checkFlowsTo(right_meet->getFirst()) && this->checkFlowsTo(right_meet->getSecond());
  //TODO support the following later
  } else if (right_quant) {
    return false;
  } else if (right_index) {
    return false;
  } else if (right_policy) {
    return false;
  } else if (right_var) {
    return false;
  } else {
    //should be unreachable
    cerr << "Unreachable, target should be some subtype of SecType" << endl;
    return false;
  }
}

bool ConstType::checkFlowsTo(SecType* other) {
  if (equals(other)) {
    return true;
  } else {
    return SecType::checkFlowsTo(other);
  }
}

SecType *ConstType::freshVars(unsigned int lineno,
                              map<perm_string, perm_string> &m) {
  return this;
}
void SecType::emitFlowsTo(SexpPrinter &printer, SecType *rhs, Module *mod) {
  JoinType *right_join     = dynamic_cast<JoinType *>(rhs);
  MeetType *right_meet     = dynamic_cast<MeetType *>(rhs);
  QuantType *right_quant   = dynamic_cast<QuantType *>(rhs);
  PolicyType *right_policy = dynamic_cast<PolicyType *>(rhs);
  if (right_join) {
    printer.startList("or");
    for (auto c : right_join->getComps()) {
      emitFlowsTo(printer, c, mod);
    }
    printer.endList();
    return;
  }
  if (right_meet) {
    printer.startList("and");
    emitFlowsTo(printer, right_meet->getFirst(), mod);
    emitFlowsTo(printer, right_meet->getSecond(), mod);
    printer.endList();
    return;
  }
  if (right_quant) {
    emitFlowsTo(printer, right_quant->getInnerType(), mod);
    return;
  }
  if (right_policy) {
    emitFlowsTo(printer, right_policy->get_lower(), mod);
    return;
  }
  printer.startList("leq");
  printer << *this << *rhs;
  printer.endList();
}

/* type variables */

VarType::VarType(perm_string varname, bool isExplicit) { varname_ = varname; _isExplicit = isExplicit; }

VarType::~VarType() {}

VarType &VarType::operator=(const VarType &t) {
  VarType *ret = new VarType(t.varname_);
  return *ret;
}

void VarType::set_type(perm_string varname) { varname_ = varname; }

perm_string VarType::get_type() const { return varname_; }

bool VarType::equals(SecType *st) {
  VarType *vt = dynamic_cast<VarType *>(st);
  if (vt != NULL) {
    return varname_ == vt->varname_;
  }
  return false;
}

SecType *VarType::freshVars(unsigned int lineno,
                            map<perm_string, perm_string> &m) {
  stringstream ss;
  ss << varname_ << lineno;
  const std::string *tmp = new string(ss.str());
  perm_string newname    = perm_string::literal(tmp->c_str());
  m[varname_]            = newname;
  return new VarType(newname);
}

bool VarType::checkFlowsTo(SecType* other) {
  if (equals(other)) {
    return true;
  } else {
    return SecType::checkFlowsTo(other);
  }
}
list<str_or_num> rllist(1, perm_string::literal("ReadLabel"));
list<str_or_num> wllist(1, perm_string::literal("WriteLabel"));
IndexType *IndexType::RL = new IndexType(perm_string::literal("Par"), rllist);
IndexType *IndexType::WL = new IndexType(perm_string::literal("Par"), wllist);

IndexType::IndexType(perm_string name, const list<str_or_num> &exprs, bool isExplicit) {
  name_  = name;
  exprs_ = exprs;
  _isExplicit = isExplicit;
}

IndexType::~IndexType() {}

IndexType &IndexType::operator=(const IndexType &t) {
  IndexType *ret = new IndexType(t.name_, t.exprs_);
  return *ret;
}

void IndexType::set_type(const perm_string name, list<str_or_num> &exprs) {
  name_  = name;
  exprs_ = exprs;
}

perm_string IndexType::get_name() const { return name_; }

list<str_or_num> IndexType::get_exprs() const { return exprs_; }

SecType *IndexType::subst(perm_string e1, const str_or_num &e2) {
  list<str_or_num> substlist;
  std::transform(TRANSFORM_IT(exprs_, substlist), [&](const str_or_num &n) {
    if (str_or_num(e1) == n)
      return e2;
    else
      return n;
  });
  return new IndexType(name_, substlist);
}

SecType *IndexType::subst(const map<perm_string, str_or_num> &m) {
  list<str_or_num> substlist;
  std::transform(TRANSFORM_IT(exprs_, substlist), [&](const auto &n) {
    auto str = std::get_if<perm_string>(&n);
    if (str && m.contains(*str))
      return m.at(*str);
    else
      return n;
  });

  return new IndexType(name_, substlist);
}

SecType *IndexType::next_cycle(BaseTypeMap &baseTypes, SecTypeMap &secTypes) {
  list<str_or_num> nextlist{};
  std::transform(TRANSFORM_IT(exprs_, nextlist), [&](const auto &n) {
    auto str = std::get_if<perm_string>(&n);
    if (str && baseTypes[*str]) {
      auto tmp = str_or_num(nextify_perm_string(*str));
      return tmp;
    } else
      return n;
  });
  return new IndexType(name_, nextlist);
}

bool IndexType::equals(SecType *st) {
  IndexType *it = dynamic_cast<IndexType *>(st);
  if (it != NULL) {
    return name_ == it->name_ && exprs_ == it->exprs_;
  }
  return false;
}

bool isConstStr(perm_string s) {
  const char *chars = s.str();
  int i             = 0;
  while (chars[i] != '\0') {
    if (chars[i] < '0' || chars[i] > '9') {
      return false;
    }
    i++;
  }
  return true;
}

void IndexType::collect_dep_expr(set<perm_string> &m) {
  for (auto &arg : exprs_) {
    auto str = std::get_if<perm_string>(&arg);
    if (str) {
      m.insert(*str);
      m.insert(nextify_perm_string(*str));
      // If this is a seqtype and so is its free variable, the next-cycle
      // value of the label is the dependant
    }
  }
}

SecType *IndexType::freshVars(unsigned int lineno,
                              map<perm_string, perm_string> &m) {
  list<str_or_num> substlist;
  for (auto &exp : exprs_) {
    auto str = std::get_if<perm_string>(&exp);
    if (str) {
      stringstream ss;
      ss << *str << lineno;
      auto tmp      = new string(ss.str());
      auto new_expr = perm_string::literal(tmp->c_str());
      m[*str]       = new_expr;
      substlist.emplace_back(new_expr);
    }
  }
  return new IndexType(name_, substlist);
}

bool IndexType::hasExpr(perm_string str) {
  return (std::find(exprs_.begin(), exprs_.end(), str_or_num(str)) !=
          exprs_.end());
}


void insertLblToSet(set<SecType*>& s, SecType* lbl) {
  for (auto l : s) {
    if (l->equals(lbl)) {
      return;
    }
  }
  s.insert(lbl);
}

void insertLblSetToSet(set<SecType*>& s, set<SecType*> lbls) {
  for (auto l : lbls) {
    insertLblToSet(s, l);
  }
}

//Joins should never contain other joins (unless they are nested below another type)
JoinType::JoinType(SecType *ty1, SecType *ty2, bool isExplicit) {
  _isExplicit = isExplicit;
  SecType *st1  = ty1->simplify();
  SecType *st2  = ty2->simplify();
  JoinType *jt1 = dynamic_cast<JoinType *>(st1);
  if (jt1) {
    insertLblSetToSet(this->comps_, jt1->getComps());
  } else {
    insertLblToSet(this->comps_, st1);
  }
  JoinType *jt2 = dynamic_cast<JoinType *>(st2);
  if (jt2) {
    insertLblSetToSet(this->comps_, jt2->getComps());
  } else {
    insertLblToSet(this->comps_, st2);
  }
}


JoinType::JoinType(set<SecType*>& lbls, bool isExplicit) {
  _isExplicit = isExplicit;
  for (auto l : lbls) {
    SecType *c  = l->simplify();
    JoinType *j = dynamic_cast<JoinType *>(c);
    if (j) { //don't nest joins
      insertLblSetToSet(this->comps_, j->getComps());
      } else {
      insertLblToSet(this->comps_, c);
    }
  }
}

JoinType::~JoinType() {}

void JoinType::emitFlowsTo(SexpPrinter &printer, SecType *rhs, Module *mod) {
  printer.startList("and");
  for (auto c : comps_) {
    c->emitFlowsTo(printer, rhs, mod);
  }
  printer.endList();
}

bool JoinType::checkFlowsTo(SecType* other) {
  bool result = true;
  for (auto c : comps_) {
    result &= c->checkFlowsTo(other);
  }
  return result;
}


SecType *JoinType::subst(perm_string e1, const str_or_num &e2) {
  bool modified = false;
  set<SecType*> newcomps;
  for (auto c : comps_) {
    SecType *c_new = c->subst(e1, e2);
    modified |= !c_new->equals(c);
    newcomps.insert(c_new);
  }
  if (modified) {
    SecType* nt = new JoinType(newcomps);
    return nt->simplify();
  } else {
    return this;
  }
}

SecType *JoinType::subst(const map<perm_string, str_or_num> &m) {
  bool modified = false;
  set<SecType*> newcomps;
  for (auto c : comps_) {
    SecType *c_new = c->subst(m);
    modified |= !c_new->equals(c);
    newcomps.insert(c_new);
  }
  if (modified) {
    SecType* nt = new JoinType(newcomps);
    return nt->simplify();
  } else {
    return this;
  }
}

SecType *JoinType::next_cycle(BaseTypeMap &baseTypes, SecTypeMap &secTypes) {
  bool modified = false;
  set<SecType*> newcomps;
  for (auto c : comps_) {
    SecType* c_new = c->next_cycle(baseTypes, secTypes);
    modified |= !c_new->equals(c);
    newcomps.insert(c_new);
  }
  if (modified) {
    SecType* nt = new JoinType(newcomps);
    return nt->simplify();
  } else {
    return this;
  }
}

JoinType &JoinType::operator=(const JoinType &t) {
  comps_ = t.comps_;
  return *this;
}

SecType *JoinType::simplify() {
  if (isBottom())
    return ConstType::BOT;
  else if (isTop())
    return ConstType::TOP;
  else if (comps_.size() == 1) {
    auto elem = *comps_.begin();
    return elem->simplify();
  }
  else {
    bool modified = false;
    set<SecType*> new_comps;
    for (auto c : comps_) {
      SecType* c_new = c->simplify();
      if (c_new->isBottom()) {
        modified = true;
        //just remove it!
        if (c_new != c) {
          delete c_new;
        }
      } else {
        modified |= !c_new->equals(c);
        new_comps.insert(c_new);
      }
    }
    if (modified) {
      if (new_comps.size() > 1) {
        return new JoinType(new_comps);
      } else if (new_comps.size() == 1) {
        return *(new_comps.begin());
      } else {
        throw std::runtime_error("Unreachable empty join after simplification");
      }
    } else {
      return this;
    }
  }
}

bool JoinType::equals(SecType *st) {
  JoinType *ct = dynamic_cast<JoinType *>(st);
  if (ct != NULL && ct->comps_ == comps_) {
    return true;
  } else {
    return SecType::equals(st);
  }
}

void JoinType::collect_dep_expr(set<perm_string> &m) {
  for (auto c : comps_) {
    c->collect_dep_expr(m);
  }
}

SecType *JoinType::freshVars(unsigned int lineno,
                             map<perm_string, perm_string> &m) {
  set<SecType*> newcomps;
  for (auto c: comps_) {
    newcomps.insert(c->freshVars(lineno, m));
  }
  return new JoinType(newcomps);
}

bool JoinType::hasExpr(perm_string str) {
  for (auto c : comps_) {
    if (c->hasExpr(str)) {
      return true;
    }
  }
  return false;
}

bool JoinType::hasTypeVar() {
  for (auto c : comps_) {
      if (c->hasTypeVar()) {
        return true;
      }
    }
    return false;
}
////////////////////////////////////////////////

MeetType::MeetType(SecType *ty1, SecType *ty2, bool isExplicit) {
  comp1_ = ty1;
  comp2_ = ty2;
  _isExplicit = isExplicit;
}

MeetType::~MeetType() {}

SecType *MeetType::getFirst() { return comp1_; }

SecType *MeetType::getSecond() { return comp2_; }

SecType *MeetType::subst(perm_string e1, const str_or_num &e2) {
  SecType *comp1new = comp1_->subst(e1, e2);
  SecType *comp2new = comp2_->subst(e1, e2);
  if (comp1_ != comp1new || comp2_ != comp2new)
    return new MeetType(comp1_->subst(e1, e2), comp2_->subst(e1, e2));
  else
    return this;
}

SecType *MeetType::subst(const map<perm_string, str_or_num> &m) {
  SecType *comp1new = comp1_->subst(m);
  SecType *comp2new = comp2_->subst(m);
  if (comp1_ != comp1new || comp2_ != comp2new)
    return new MeetType(comp1_->subst(m), comp2_->subst(m));
  else
    return this;
}

SecType *MeetType::next_cycle(BaseTypeMap &baseTypes, SecTypeMap &secTypes) {
  SecType *comp1new = comp1_->next_cycle(baseTypes, secTypes);
  SecType *comp2new = comp2_->next_cycle(baseTypes, secTypes);
  if (comp1_ != comp1new || comp2_ != comp2new)
    return new MeetType(comp1_->next_cycle(baseTypes, secTypes), comp2_->next_cycle(baseTypes, secTypes));
  else
    return this;
}

MeetType &MeetType::operator=(const MeetType &t) {
  MeetType *ret = new MeetType(t.comp1_, t.comp2_);
  return *ret;
}

SecType *MeetType::simplify() {
  if (isBottom())
    return ConstType::BOT;
  else if (isTop())
    return ConstType::TOP;
  else {
    if (comp1_->isTop())
      return comp2_->simplify();
    else if (comp2_->isTop())
      return comp1_->simplify();
    else {
      SecType *lsimpl = comp1_->simplify();
      SecType *rsimpl = comp2_->simplify();
      if (lsimpl->equals(rsimpl)) {
        return lsimpl;
      } else {
        return new MeetType(lsimpl, rsimpl, _isExplicit);
      }
    }
  }
}

bool MeetType::equals(SecType *st) {
  MeetType *ct = dynamic_cast<MeetType *>(st);
  if (ct != NULL) {
    return comp1_->equals(ct->comp1_) && comp2_->equals(ct->comp2_);
  }
  return false;
}

void MeetType::collect_dep_expr(set<perm_string> &m) {
  comp1_->collect_dep_expr(m);
  comp2_->collect_dep_expr(m);
}

SecType *MeetType::freshVars(unsigned int lineno,
                             map<perm_string, perm_string> &m) {
  return new MeetType(comp1_->freshVars(lineno, m),
                      comp2_->freshVars(lineno, m));
}

bool MeetType::hasExpr(perm_string str) {
  return comp1_->hasExpr(str) || comp2_->hasExpr(str);
}

bool MeetType::hasTypeVar() {
  return comp1_->hasTypeVar() || comp2_->hasTypeVar();
}

void MeetType::emitFlowsTo(SexpPrinter &printer, SecType *rhs, Module *mod) {
  printer.startList("or");
  getFirst()->emitFlowsTo(printer, rhs, mod);
  getSecond()->emitFlowsTo(printer, rhs, mod);
  printer.endList();
}
bool MeetType::checkFlowsTo(SecType* other) {
  return getFirst()->checkFlowsTo(other) || getSecond()->checkFlowsTo(other);
}
//---------------------------------------------
// QuantType
//---------------------------------------------
QuantType::QuantType(perm_string index_var, SecType *type, bool isExplicit) {
  _index_var = index_var;
  _name      = lex_strings.make("TODO");
  _sectype   = type;
  _isExplicit = isExplicit;
}
bool QuantType::hasTypeVar() {
  return _sectype->hasTypeVar();
}

void QuantType::collect_dep_expr(set<perm_string> &m) {
  bool remove_quantvar = m.find(_index_var) == m.end();
  _sectype->collect_dep_expr(m);
  if (remove_quantvar) {
    std::set<perm_string>::iterator it = m.find(_index_var);
    if (it != m.end()) {
      m.erase(it);
      it = m.find(nextify_perm_string(_index_var));
      m.erase(it);
    }
  }
}

SecType *QuantType::next_cycle(BaseTypeMap &baseTypes, SecTypeMap &secTypes) {
  return new QuantType(_index_var, _sectype->next_cycle(baseTypes, secTypes));
}
//----------------------------------------------
// Policy Type
//----------------------------------------------

PolicyType::PolicyType(SecType *lower, perm_string cond_name,
                       const list<str_or_num> &static_exprs,
                       const list<str_or_num> &dynamic_exprs, SecType *upper, bool isExplicit) {
  _isNext    = false;
  _lower     = lower;
  _cond_name = cond_name;
  _static    = static_exprs;
  _dynamic   = dynamic_exprs;
  _upper     = upper;
  _isExplicit = isExplicit;
}

bool PolicyType::equals(SecType *st) {
  PolicyType *pt = dynamic_cast<PolicyType *>(st);
  if (!pt) {
    return false;
  } else {
    return _lower->equals(pt->_lower) && _upper->equals(pt->_upper) &&
           _cond_name == pt->_cond_name && _static == pt->_static &&
           _dynamic == pt->_dynamic;
  }
}

SecType *PolicyType::next_cycle(BaseTypeMap &baseTypes, SecTypeMap &secTypes) {
  list<str_or_num> *nextlist = new list<str_or_num>;
  for (auto &dyn : _dynamic) {
    perm_string *str = std::get_if<perm_string>(&dyn);
    if (str && baseTypes.contains(*str) && baseTypes.at(*str) &&
        baseTypes.at(*str)->isSeqType()) {
      nextlist->push_back(nextify_perm_string(*str));
    } else {
      nextlist->push_back(dyn);
    }
  }
  PolicyType *res = new PolicyType(_lower->next_cycle(baseTypes, secTypes), _cond_name, _static,
                                   *nextlist, _upper->next_cycle(baseTypes, secTypes));
  res->_isNext    = true;
  return res;
}

bool PolicyType::hasExpr(perm_string str) {
  return (std::find(_static.begin(), _static.end(), str_or_num(str)) !=
          _static.end()) ||
         (std::find(_dynamic.begin(), _dynamic.end(), str_or_num(str)) !=
          _dynamic.end()) ||
         _lower->hasExpr(str) || _upper->hasExpr(str);
}

bool PolicyType::hasTypeVar() {
  return _lower->hasTypeVar() || _upper->hasTypeVar();
}

SecType *PolicyType::subst(perm_string e1, const str_or_num &e2) {
  SecType *nlower = _lower->subst(e1, e2);
  SecType *nupper = _upper->subst(e1, e2);
  auto do_subst   = [&](const str_or_num &n) {
    if (n == str_or_num(e1))
      return str_or_num(e2);
    else
      return n;
  };
  list<str_or_num> staticlist;
  std::transform(TRANSFORM_IT(_static, staticlist), do_subst);
  list<str_or_num> dynamiclist;
  std::transform(TRANSFORM_IT(_dynamic, dynamiclist), do_subst);
  return new PolicyType(nlower, _cond_name, staticlist, dynamiclist, nupper);
}

SecType *PolicyType::subst(const map<perm_string, str_or_num> &m) {
  SecType *nlower = _lower->subst(m);
  SecType *nupper = _upper->subst(m);
  auto do_subst   = [&m](const str_or_num &n) {
    auto *str = std::get_if<perm_string>(&n);
    if (str && m.contains(*str))
      return str_or_num(m.at(*str));
    else
      return n;
  };

  list<str_or_num> staticlist;
  std::transform(TRANSFORM_IT(_static, staticlist), do_subst);
  list<str_or_num> dynamiclist;
  std::transform(TRANSFORM_IT(_dynamic, dynamiclist), do_subst);
  return new PolicyType(nlower, _cond_name, staticlist, dynamiclist, nupper);
}
void PolicyType::collect_dep_expr(set<perm_string> &m) {
  _lower->collect_dep_expr(m);
  _upper->collect_dep_expr(m);
  auto collect = [&m](const str_or_num &n) {
    auto str = std::get_if<perm_string>(&n);
    if (str) {
      m.insert(*str);
      // If this is a seqtype and so is its free variable, the next-cycle
      // value of the label is the dependand
      // ^^ who tf knows what this means but it's been here before I
      m.insert(nextify_perm_string(*str));
    }
  };
  std::for_each(CONST_IT(_static), collect);
  std::for_each(CONST_IT(_dynamic), collect);
}

void PolicyType::emitFlowsTo(SexpPrinter &printer, SecType *rhs, Module *mod) {
  PolicyType *right_policy = dynamic_cast<PolicyType *>(rhs);
  ConstType *right_const   = dynamic_cast<ConstType *>(rhs);
  VarType *right_var       = dynamic_cast<VarType *>(rhs);
  IndexType *right_index   = dynamic_cast<IndexType *>(rhs);
  if (right_const || right_var || right_index) {
    get_upper()->emitFlowsTo(printer, rhs, mod);
    return;
  }
  if (right_policy) {
    printer.startList("or");
    get_upper()->emitFlowsTo(printer, right_policy->get_lower(), mod);
    printer.startList("and");
    // lower bound to lower bound
    get_lower()->emitFlowsTo(printer, right_policy->get_lower(), mod);
    // upper bound to upper bound
    get_upper()->emitFlowsTo(printer, right_policy->get_upper(), mod);
    // only emit erasure check if target is next cycle
    if (right_policy->isNextType()) {
      printer.startList("not");
      auto arglist = get_all_args();
      dumpZ3Func(printer, _cond_name, arglist);
      printer.endList();
    }
    // erasure condition must be at least as strong
    // quantify over all possible static variables
    std::set<string> quantlist;
    std::list<str_or_num> leftlist;
    std::list<str_or_num> rightlist;
    std::map<perm_string, perm_string> submap;
    printer.startList("forall");
    printer.startList();

    for (auto &lq : _static) {
      string s = string("quant_");
      s += std::visit(str_or_num_to_string(), lq);
      perm_string ns = lex_strings.make(s.c_str());
      quantlist.insert(s);
      leftlist.emplace_back(ns);
      if (auto *v = std::get_if<perm_string>(&lq)) {
        submap[*v] = ns;
      }
    }

    for (auto &rq : right_policy->get_static()) {
      string s = string("quant_");
      s += std::visit(str_or_num_to_string(), rq);
      perm_string ns = lex_strings.make(s.c_str());
      quantlist.insert(s);
      rightlist.emplace_back(ns);
      if (auto *v = std::get_if<perm_string>(&rq)) {
        submap[*v] = ns;
      }
    }

    for (auto &q : quantlist) {
      printer.startList(q);
      printer << "Int";
      printer.endList();
    }
    printer.endList(); // end quant variable decl

    printer.startList("implies");
    printer.startList("and");
    for (auto &qp : submap) {
      printer.startList("<=");
      printer << "0" << qp.second.str();
      printer.endList();
      printer.startList("<=");
      printer << qp.second.str()
              << std::to_string((1 << (mod->wires[qp.first]->getRange() + 1)) -
                                1);
      printer.endList();
    }

    // rename any static variables in the assumptions with
    // their new quant names
    PExpr *assumption = mod->getAssumptions();
    if (assumption) {
      Predicate tmp;
      Hypothesis h(assumption);
      tmp.hypotheses.insert(&h);
      printer << *tmp.subst(submap);
    }
    printer.endList(); // end and

    // append all (non quantified) dynamic variables
    leftlist.insert(leftlist.end(), CONST_IT(_dynamic));

    const auto &rdynamic = right_policy->get_dynamic();
    rightlist.insert(rightlist.end(), CONST_IT(rdynamic));

    printer.startList("implies");
    dumpZ3Func(printer, _cond_name, leftlist);
    dumpZ3Func(printer, right_policy->get_cond(), rightlist);
    printer.endList();

    printer.endList(); // end assumption and bound implies
    printer.endList();
    printer.endList();
    printer.endList();
    return;
  }
  // else do super class behavior
  SecType::emitFlowsTo(printer, rhs, mod);
}
////////////////////////////

Hypothesis *Hypothesis::subst(map<perm_string, perm_string> m) {
  return new Hypothesis(bexpr_->subst(m));
}

bool Hypothesis::matches(perm_string name) {
  return bexpr_->contains_expr(name);
}

// TypeEnv &TypeEnv::operator=(const TypeEnv &e) {
//   TypeEnv *ret = new TypeEnv(e);
//   return *ret;
// }

Predicate &Predicate::operator=(const Predicate &p) {
  Predicate *ret  = new Predicate();
  ret->hypotheses.insert(p.hypotheses.begin(), p.hypotheses.end());
  return *ret;
}

Predicate *Predicate::subst(map<perm_string, perm_string> m) const {
  Predicate *ret = new Predicate();
  for (set<Hypothesis *>::iterator ite = hypotheses.begin();
       ite != hypotheses.end(); ite++) {
    ret->hypotheses.insert(new Hypothesis((*ite)->bexpr_->subst(m)));
  }
  return ret;
}

void _dump_const_internal(SexpPrinter &printer, Constraint &c,
  std::set<perm_string> genvars, TypeEnv &env, bool isAssumption) {
  dump_genvar_pred(printer, genvars, env);
  printer.startList("assert");

  bool hashypo = c.pred != NULL && c.pred->hypotheses.size() != 0;

  if (hashypo) {
  printer.startList("and");
  }
  if (hashypo) {
  printer << (*c.pred);
  }

  if (!isAssumption) {
    printer.startList("not"); //For assumptions, just assert them!
  }
  
  c.right->simplify()->emitFlowsTo(printer, c.left->simplify(), env.module);
  
  if (!isAssumption) {
    printer.endList();
  }
  
  if (hashypo) {
    printer.endList();
  }

  printer.endList(); // end assert
}

void dump_constraint(SexpPrinter &printer, Constraint &c,
                     std::set<perm_string> genvars, TypeEnv &env) {
 _dump_const_internal(printer, c, genvars, env, false);
}

void dump_assumption(SexpPrinter &printer, Constraint &c,
  std::set<perm_string> genvars, TypeEnv &env) {
  _dump_const_internal(printer, c, genvars, env, true);
}
void dump_equality_constraint(SexpPrinter &printer, SecType* l, SecType* r) {
  printer.startList("assert");
  printer.startList("=");
  l->dump(printer);
  r->dump(printer);
  printer.endList();
  printer.endList();
}
