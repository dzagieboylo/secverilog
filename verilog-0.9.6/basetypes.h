#ifndef __basetypes_H
#define __basetypes_H

class BaseType {
public:
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

#endif
