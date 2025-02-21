#ifndef __basetypes_H
#define __basetypes_H

#include <map>
#include "StringHeap.h"

class BaseType {
public:
  virtual ~BaseType() {}
  virtual const char *name() { return "BaseType"; }
  virtual bool isSeqType() { return false; }
  virtual bool isNextType() { return false; }
  virtual bool isExplicit() { return _isExplicit; }
protected:
  bool _isExplicit = false;

};
class ComType : public BaseType {
public:
  ComType(bool isExplicit = false);
  virtual const char *name() { return "ComType"; }
};
class SeqType : public BaseType {
public:
  SeqType(bool isExplicit = false);
  virtual const char *name() { return "SeqType"; }
  virtual bool isSeqType() { return true; }
};

class NextType : public BaseType {
public:
  NextType(bool isExplicit = false);
  virtual const char *name() { return "NextType"; }
  virtual bool isNextType() { return true; }
};

using BaseTypeMap = std::map<perm_string, BaseType *>;

#endif
