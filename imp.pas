//////////////////////////////////////////////////////////////
// implish: an imperative meta-programming language.
//
// Copyright 2013 Michal J Wallace <http://tangentstorm.com/>
// Avaliable to the public for use under the MIT/X11 License.
//--------------------------------------------------------------
// This unit can be compiled as a program by defining the symbol
// symbol IMPSHELL during compilation. The Makefile generates
// an interface section automatically.
//////////////////////////////////////////////////////////////
{$mode objfpc}{$i xpc.inc}
{ }{$IFNDEF IMPSHELL} // { } so the pre-processor won't see it
unit imp;
interface {$I imp.def} implementation
{ }{$ELSE}
program imp;
{ }{$ENDIF}
uses xpc, arrays, stacks, ascii, sysutils, strutils, num, variants,
  math {$IFNDEF NOPROMPT}, cx, lined{$ENDIF};

procedure halt( msg : string );
  begin
    writeln( msg );
    system.halt(-1);
  end;

//== meta model ================================================

// The model presented here is largely based on John McCarthy's
// LISP system, described in his 1960 paper, "Recursive Functions
// of Symbolic Expressions and Their Computation by Machine, Part I"
// http://www-formal.stanford.edu/jmc/recursive/
//
// Specifically, we're translating this page:
//
//    http://www-formal.stanford.edu/jmc/recursive/node3.html

//-- a. symbolic expressions -----------------------------------

// In order to work with several kinds of symbolic expressions,
// we adopt a universal representation, consisting of a 'kind'
// marker and an integer.
//
// When x.kind=kINT, x.data represents the integer itself. In all
// other cases, the data field is either ignored or used as a key
// to find the actual value in a lookup table.
{$IFDEF IMPSHELL}
type
  TKind = (
    kSYM,  // an symbol or 'atom', represented internally by a string
    kNUL,  // NULL, a special symbol. Represents false and the empty list.
    kERR,  // used to represent error conditions
    kEOF,  // end of file marker
    kSTR,  // alternate symbol syntax with quotes to allow spaces
    kINT,  // an integer
    kCEL,  // a 'cons cell' (pair of sybols)
    kMF0,  // a meta-procedure (a:TExpr -> (), implemented in pascal)
    kMF1,  // a meta-function (a:TExpr -> TExpr, implemented in pascal)
    kMF2,  // a meta-function (a,b:TExpr -> TExpr)
    kMF3,  // a meta-function (a,b,c:TExpr -> TExpr)
    kMF4); // a meta-function (a,b,c,d:TExpr -> TExpr)

  TExpr = record
    kind : TKind;
    data : integer;
  end;
{$ENDIF}

{ }{$IFDEF IMPSHELL}
{ }function ShowExpr( expr : TExpr ) : string; forward;
{ }{$ENDIF}

// Sx() provides a universal constructor for s-expressions.
function Sx( kind : TKind; data : integer ) : TExpr;
  begin
    result.kind := kind;
    result.data := data;
  end; { Sx }

// - atoms - - - - - - - - - - - - - - - - - - - - - - - - - - -
// Any s-expression where kind<>kCEL is an atom.
const atomic = [kSYM..kMF4] - [kCEL];

// We can represent Symbols, NULL, Errors, and String atoms
// as strings in pascal, and store values for all of them in
// the same lookup table:
type TSymTbl = specialize arrays.GEqArray<string>;
var syms : TSymTbl;

// Key() converts a string to an integer, representing its
// position in the lookup table.
function Key( s :  string ) : cardinal;
  begin
    if not syms.Find( s, result ) then result := syms.Append( s );
  end; { Key }

// To expose a symbolic name to the interpreter, we can create
// symbols with Sx(kSYM, Key('name')), but it would be nicer if
// we could simplify it to Sym('name'). So:
function Sym( s : string ) : TExpr;
  begin
    result := Sx(kSYM, Key(s))
  end;

function Err( s : string ) : TExpr;
  begin
    result := Sx(kERR, Key(s))
  end;

// - cells - - - - - - - - - - - - - - - - - - - - - - - - - - -
// An S-expression where kind=kCEL is a cell. Cells are simply
// pairs of s-expressions. For historical reasons, these are
// called car and cdr in lisp. Will use records to represent
// the cells, and store them in a dynamic array.
type
  TCell = record
            car, cdr : TExpr
          end;

// 'cells' is the the global table of cells.
type TCellTbl = specialize arrays.GArray<TCell>;
var cells : TCellTbl;

//-- b. meta-functions ---------------------------------------

// McCarthy used the m-expression syntax as a meta-language to
// describe how to evaluate S-expressions. ('m' is for 'meta')
// Since we're using pascal for our meta language, we translate
// m-expressions to pascal functions. We will allow defining
// variables of up to 5 arguments.
{$IFDEF IMPSHELL}
type
  TMetaFun0 = function : TExpr;
  TMetaFun1 = function (a : TExpr) : TExpr;
  TMetaFun2 = function (a,b : TExpr) : TExpr;
  TMetaFun3 = function (a,b,c : TExpr) : TExpr;
  TMetaFun4 = function (a,b,c,d : TExpr) : TExpr;

// An s-expression of kind=kMFx is therefore not an M-expression
// but a symbol that represents a particular pascal function of
// one of these types.
//
// Note that we are not limited to the functions McCarthy gave us.
// Any pascal code can be exposed to our interpreter by creating
// a meta-function.
//
// I would therefore prefer to store metas in a dynamic array like
// the other types (using 'arrays.GArray'), but the version of free
// pascal I'm using has a bug[1] that prevents it. Until that's fixed,
// we're stuck with a static array.
//
// [1] http://bugs.freepascal.org/view.php?id = 25002
type
  TArity = 0..4;
  TMetaTbl = array [byte] of record
    case arity:TArity of
      0 : (f0: TMetaFun0);
      1 : (f1: TMetaFun1);
      2 : (f2: TMetaFun2);
      3 : (f3: TMetaFun3);
      4 : (f4: TMetaFun4);
    end;
const
  aritykind : array[TArity] of TKind = (kMF0, kMF1, kMF2, kMF3, kMF4);
{$ENDIF}
var
  metas     : TMetaTbl;
  metacount : byte = 0;

// Meta adds a function record to the 'metas' table and constructs
// a unique symbol for it.
function NextMeta( a : TArity; p : pointer ) : TExpr;
  begin
    if metacount = high(metas) then
      halt( 'out of meta slots.' )
    else begin
      with metas[metacount] do begin
        arity := a;
        case arity of
          0: f0 := TMetaFun0(p);
          1: f1 := TMetaFun1(p);
          2: f2 := TMetaFun2(p);
          3: f3 := TMetaFun3(p);
          4: f4 := TMetaFun4(p);
        end
      end;
      result := Sx(aritykind[a], metacount);
      inc(metacount);
    end
  end;

function Meta( f : TMetaFun0 ) : TExpr; overload;
  begin result := NextMeta(0, f) end;

function Meta( f : TMetaFun1 ) : TExpr; overload;
  begin result := NextMeta(1, f) end;

function Meta( f : TMetaFun2 ) : TExpr; overload;
  begin result := NextMeta(2, f) end;

function Meta( f : TMetaFun3 ) : TExpr; overload;
  begin result := NextMeta(3, f) end;

function Meta( f : TMetaFun4 ) : TExpr; overload;
  begin result := NextMeta(4, f) end;

// We will populate this table in section e2.

// - debugger - - - - - - - - - - - - - - - - - - - - - - - - -

function trace(step:string; e : TExpr) : boolean;
  var cmd: string;
  begin
    writeln( step, ':', ShowExpr(e));
    {$IFDEF NOPROMPT} readln(cmd);
    {$ELSE}  lined.prompt('debug>', cmd);
    {$ENDIF}
    if cmd = 'q' then halt('goodbye');
    result := true;
  end;


//-- c. elementary meta-expressions ----------------------------

// These are the elementary expressions from the 1960 LISP paper.
//
// The m prefix used in these routines is short for 'meta', since
// we're using pascal as a meta-language to describe lisp. As a
// convention, we will also type meta function names in ALL CAPS.

// 1. atom[x] -> T if x is an atom, else F
function mATOM( x : TExpr ) : boolean;
  begin
    result := x.kind in atomic
  end; { mATOM }

// 2. eq[x;y] = atom[x] ? atom[y] ? x = y | F | undefined
// We'll just treat the undefined case as false.
function mEQ( x, y : TExpr ) : boolean;
  begin
    result := mATOM(x) and mATOM(y)
      and (x.kind = y.kind)
      and (x.data = y.data)
  end; { mEQ }

// 3. car[x] = atom[x] ? undefined | x0 where x = (x0, x1)
// We'll use an error symbol for the undefined case.
function mCAR( x : TExpr ) : TExpr;
  begin
    if mATOM(x) then result := Sx(kErr, Key('!CAR[atom]'))
    else result := cells[x.data].car
  end; { mCAR }

// 4. cdr[x] = atom[x] ? undefined | x1 where x = (x0, x1)
function mCDR( x : TExpr ) : TExpr;
  begin
    if mATOM(x) then result := Sx(kErr, Key('!CDR[atom]'))
    else result := cells[x.data].cdr
  end; { mCDR }

// 5. cons[x;y] -> (x, y)
function mCONS( x, y : TExpr ) : TExpr;
  var cell : TCell;
  begin
    cell.car := x;
    cell.cdr := y;
    result := Sx( kCEL, cells.Append( cell ));
  end; { mCons }

// - predicates - - - - - - - - - - - - - - - - - - - - - - - - -

// McCarthy's first two elementary expressions translated to the
// type (TExpr -> boolean) so that we could use them in pascal,
// but it would be nice to use also treat them as (TExpr -> TExpr)
// so that we can add them to the 'metas' table.

// In order to do this, we will provide pascal names for the
// symbols T and F. In modern lisp, F is written as () or NIL,
// representing both falsehood and the empty list. Since these
// result in a syntax error and a type error in pascal (NIL is
// already defined as the default pointer value), we will call
// the symbol NULL.
{$IFDEF IMPSHELL}
var { boolean symbols }
  sNULL : TExpr;
  sTRUE : TExpr;
{$ENDIF}

// We will call this routine at startup to initialize them:
procedure CreateBooleans;
  begin
    sNULL := Sx(kNUL, Key('()'));
    sTRUE := Sx(kSYM, Key('T'));
  end;

// To translate:

// EnBool encodes a pascal boolean as an s-expression:
function EnBool( b : boolean ) : TExpr;
  begin
    if b then result := sTRUE else result := sNULL
  end;

// ExBool extracts a pascal boolean from an s-expression.
function ExBool( x : TExpr ) : boolean;
  begin
    result := x.kind <> kNUL
  end;

// We can now define new versions of mATOM and mEQ as TExpr->TExpr.
// Following lisp tradiion, the P suffix is used both as an
// abbreviation for the word 'predicate' and for its resemblence
// to a question mark.

function mATOMP( x : TExpr ) : TExpr;
  begin
    result := EnBool( mATOM( x ))
  end;

function mEQP( x, y : TExpr ) : TExpr;
  begin
    result := EnBool( mEQ( x, y ))
  end;

//-- d. recursive meta-functions -------------------------------

// 1. ff[x] -> first atomic symbol in f, ignoring parentheses.
// Perhaps this is an abbreviation for "find first".
// Note: this works but it's not necessary for mEVAL, so I
// don't include it in the binary.
{ function mFF( x : TExpr ) : TExpr;
  begin
    if mATOM(x) then result := x else result := mFF(mCAR(x))
  end; }

// 2. subst[x;y;z] -> copy z, replacing each occurrence of y with x.
function mSUBST( x, y, z : TExpr ) : TExpr;
  begin
    if mATOM(z) then
      if mEQ(z, y) then result := x
      else result := z
    else result := mCONS(mSUBST(x, y, mCAR(z)),
                         mSUBST(x, y, mCDR(z)))
  end;

// 3. equal[x;y] -> T if x and y are the same, else F
function mEQUAL( x, y : TExpr ) : TExpr;
  begin
    result := EnBool(
      ( mATOM(x) and mATOM(y) and mEQ(x, y) )
      or ( not ( mATOM(x) or mATOM(y) )
           and mEQ(MCAR(x), mCAR(y))
           and mEQ(mCDR(x), mCDR(y)) ) )
  end;

// 4. null?(x) -> T if x = NIL else F
function mNULL( x : TExpr ) : boolean;
  begin
    result := mEQ(x, sNULL)
  end;

// here is the reified version:
function mNULLP( x : TExpr ) : TExpr;
  begin
    result := mEQP(x, sNULL)
  end;

// - abbreviations - - - - - - - - - - - - - - - - - - - - - - -

// caar[x] -> car[car[x]]
function mCAAR( x : TExpr ) : TExpr;
  begin
    result := mCAR(mCAR(x))
  end;

// cadr[x] -> car[cdr[x]]
function mCADR( x : TExpr ) : TExpr;
  begin
    result := mCAR(mCDR(x))
  end;

function mCDDR( x : TExpr ) : TExpr;
  begin
    result := mCDR(mCDR(x))
  end;

// cadar[x] -> car[cdr[cdr[x]]]
function mCADAR( x : TExpr ) : TExpr;
  begin
    result := mCAR(mCDR(mCAR(x)))
  end;

// caddar[x] -> car[cdr[cdr[car[x]]]]
function mCADDAR( x : TExpr ) : TExpr;
  begin
    result := mCAR(mCDR(mCDR(mCAR(x))))
  end;

// caddr[x] -> car[cdr[cdr[x]]]
function mCADDR( x : TExpr ) : TExpr;
  begin
    result := mCAR(mCDR(mCDR(x)))
  end;

function mCADDDR( x : TExpr ) : TExpr;
  begin
    result := mCAR(mCDR(mCDR(mCDR(x))))
  end;

function mCADDDDR( x : TExpr ) : TExpr;
  begin
    result := mCAR(mCDR(mCDR(mCDR(mCDR(x)))))
  end;

// - list builder - - - - - - - - - - - - - - - - - - - - - - - -

// The function L will build lists as s-sexpressions. This
// corresponds to McCarthy's suggested LIST function, but because
// it's only a convenience method for use in pascal, we will not try
// to lift it into implish. (We will have to wait to implement
// the normal lisp LIST routine until after we implement EVAL).

// So: we'll define L for up to 10 items, purely for our own
// convenience.

// With zero arguments, L() returns the empty list:
function L : TExpr;
  begin result := sNULL end;

// With one argument, L(a) returns a list with one item: a.
function L( a : TExpr ) : TExpr;
  begin result := mCONS(a, sNULL) end;

// After the first version, each successive version can simply
// CONS its first argument onto the L of the other arguments.

// Note that L with two arguments is *NOT* the same as mCONS.
// (cons a (b c)) -> (a b c)
// (list a (b c)) -> (a (b c))
function L( a, b : TExpr ) : TExpr; inline;
 begin result := mCONS(a, L(b)) end;

// The rest of these just follow the same pattern:

function L( a, b, c : TExpr ) : TExpr; inline;
  begin result := mCONS(a, L(b, c)) end;

function L( a, b, c, d : TExpr ) : TExpr; inline;
  begin result := mCONS(a, L(b, c, d)) end;

function L( a, b, c, d, e : TExpr ) : TExpr; inline;
  begin result := mCONS(a, L(b, c, d, e)) end;

function L( a, b, c, d, e, f : TExpr ) : TExpr; inline;
  begin result := mCONS(a, L(b, c, d, e, f)) end;

function L( a, b, c, d, e, f, g : TExpr ) : TExpr; inline;
  begin result := mCONS(a, L(b, c, d, e, f, g)) end;

function L( a, b, c, d, e, f, g, h : TExpr ) : TExpr; inline;
  begin result := mCONS(a, L(b, c, d, e, f, g, h)) end;

function L( a, b, c, d, e, f, g, h, i : TExpr ) : TExpr; inline;
  begin result := mCONS(a, L(b, c, d, e, f, g, h, i)) end;

function L( a, b, c, d, e, f, g, h, i, j : TExpr ) : TExpr; inline;
  begin result := mCONS(a, L(b, c, d, e, f, g, h, i, j)) end;

// - list enumerator - - - - - - - - - - - - - - - - - - - - - -

// "for x in exprs.." syntax for TExpr values.
{$IFDEF IMPSHELL}
type TExprEnumerator = class
  private
    head, cell : TExpr;
    onFirst : boolean;
    function GetCurrent : TExpr;
  public
    property Current : TExpr read GetCurrent;
    constructor Create(const x: TExpr);
    function MoveNext: boolean;
  end;
{$ENDIF}

constructor TExprEnumerator.Create(const x:TExpr);
  begin
    if x.kind in [kNUL, kCEL] then
      begin
        self.onFirst := true;
        self.head := x
      end
    else raise Exception.Create('not a list')
  end;

function TExprEnumerator.GetCurrent : TExpr;
  begin
    result := mCAR(self.cell)
  end;

function TExprEnumerator.MoveNext: boolean;
  begin
    if self.onFirst then
      begin
        self.cell := self.head;
        self.onFirst := false
      end
    else self.cell := mCDR(self.cell);
    result := self.cell.kind = kCEL;
  end;

operator Enumerator(const x: TExpr): TExprEnumerator;
  begin
    result := TExprEnumerator.Create(x)
  end;

// - functions - - - - - - - - - - - - - - - - - - - - - - - - -

// append[x;y] -> append y to x
function mAPPEND( x, y : TExpr ) : TExpr;
  begin
    if mNULL(x) then result := y
    else result := mCONS(mCAR(x), mAPPEND(mCDR(x), y))
  end;

// among [x;y] = ~null[y] ^ [equal [x;car [y]] | among [x;cdr[y]]]
// is x in list y?
function mAMONG( x, y : TExpr ) : boolean;
  begin
    result := mEQ(x,mCAR(y)) or mAMONG(x, mCDR(y))
  end;

function mAMONGP( x, y : TExpr ) : TExpr;
  begin
    result := EnBool(mAMONG(x, y))
  end;

// zip -- McCarthy calls this 'pair'. 'zip' comes from haskell and python.
function mZIP( x, y : TExpr ) : TExpr;
  begin
    if mATOM(x) or mATOM(y) then result := sNULL
    else result := mCONS(L(mCAR(x), mCAR(y)),
                         mZIP(mCDR(x), mCDR(y)))
  end;

// assoc[s;a] look up symbol s in alist a where a = ((k0,v0) (k1,v1) ...)
function mASSOC( s, a : TExpr ) : TExpr;
  begin
    if mNULL(a) then result := Err('!ASSOC[' + ShowExpr(s) + ']')
    else if mEQ(mCAAR(a), s) then result := mCADAR(a)
    else result := mASSOC(s, mCDR(a))
  end;

// sublis[x;y] -> subst uN->vN in y, where x=((u0,v0), (u1,v1)...)
function mSUBLIS( x, y : TExpr ) : TExpr;
  function SUB2( x, z : TExpr ) : TExpr;
    begin
      if mNULL(x) then result := z
      else if mEQ(mCAAR(x), z) then result := mCADAR(x)
      else result := SUB2(mCDR(x), z)
    end;
  begin { mSUBLIS }
    if mATOM(x) then result := SUB2(x, y)
    else result := mCONS(mSUBLIS(x, mCAR(y)), mSUBLIS(x, mCDR(y)))
  end;

//-- e. functions as s-expressions -----------------------------

// In this section, McCarthy provides the rules for rewriting
// m-expressions as s-expressions.

// In pascal, our meta-language consitsts of the Sx()
// function, our various meta-functions, and the variables
// sTRUE and sNULL.

// To translate our meta-notation to the symbolic notation, we
// will can create a symbol where kind=kMF** for each function,
// and add it to the 'metas' array we created earlier.

// Let's consider each of his translation rules, in order.
// Following McCarthy's lead, we'll use the notation E* to
// represents the s-expression translation of m-expression E.

// e1.QUOTE
// e4.COND
// e5.LAMBDA and
// e6.LABEL
//
// In McCarthy's lisp, these four forms are not functions,
// but rather 'special forms': symbols that cause the evaluator
// to do something other than apply a function to its arguments.

var
  sQUOTE, sCOND, sLAMBDA, sLABEL, sENV, sDEF : TExpr;

// q() is just a utility function for writing quotes in pascal :
function q(x:TExpr) : TExpr;
  begin
    result := L(sQUOTE, x)
  end; { q }

// Once again, we'll create a procedure to initialize these
// for us and invoke the procedure at startup.
procedure CreateSpecials;
  begin
    sQUOTE  := Sym('quote');
    sCOND   := Sym('cond');
    sLAMBDA := Sym('lambda');
    sLABEL  := Sym('label');
    sENV    := Sym('env');
    sDEF    := Sym('def');
  end;

// e2. "Variables and function names that were represented by strings of
// lower-case letters are translated to the corresponding strings of the
// corresponding uppercase letters. Thus car* is CAR and subst* is SUBST."
//
// In pascal, we can use the @ operator ('address-of') to refer to a
// function or procedure without actually calling it. Thus, to refer
// to the mCAR function, we could write @mCAR.
//
// Earlier, we defined Meta(), which allows us to create a symbol
// (with .kind in [kMF0..kMF4]) for any of our meta-functions.
// However, these values don't have a very user-friendly symbolic
// representation. (In the interpreter, we just render them as:
// <0>, <1> .. <n> for the record stored in metas[n])
//
// It would be nicer to refer to functions by name, both in the
// interpreter and in pascal code.
//
// For functions, though, it would be nicer still to declare a variable.
// For clarity and to avoid name collisions, we will follow the
// convention of prefixing variables of type TExpr and kind=kSYM with
// the prefix 's'. (We've already been doing this with sTRUE and sNULL.)
// Then we can refer to mCAR symbolically as sCar, mSUBST as sSubst, etc.
//
// We will create such a symbol now for all of the routines
// of type (TExpr -> TExpr) that we've defined so far, as well as
// the ones we're going to define later in the file.
{$IFDEF IMPSHELL}
var
  // the functions we've defined so far:
  sAtomP, sEqP, sCar, sCdr, sCons, sSubst, sEqualP, sNullP,
  sCaar, sCadr, sCadar, sCaddr, sAppend, sAmongP, sZip,
  sAssoc, sSublis,

  // and now the ones we'll define later ...
  sApply, sEval, sAppq,
  sList, sMapList, sSearch, sFilter, sReduce,
  sAdd, sSub, sMul, sDiv, sMod, sPow,
  sReadFile, sWriteFile, sBinRead, sBinWrite,
  sArray, sLen, sPush, sPop,
  sSym2Chars, sChars2Sym
  : TExpr;

{$ENDIF}
{ }{$IFDEF IMPSHELL}
  // ... for which we also have to provide forward declarations,
  // so we can refer to them when creating the kind=kMFx symbols:
  function mAPPLY  ( f, args, env : TExpr ) : TExpr; forward;
  function mEVAL   ( e, a : TExpr ) : TExpr; forward;
  function mAPPQ   ( m : TExpr ) : TExpr; forward;
  function mLIST   ( x : TExpr ) : TExpr; forward;

  function mMAPLIST ( f, x : TExpr ) : TExpr; forward;
  function mSEARCH  ( f, x : TExpr ) : TExpr; forward;
  function mFILTER  ( f, x : TExpr ) : TExpr; forward;
  function mREDUCE  ( f, x, y : TExpr ) : TExpr; forward;

  function mADD ( x, y : TExpr ) : TExpr; forward;
  function mSUB ( x, y : TExpr ) : TExpr; forward;
  function mMUL ( x, y : TExpr ) : TExpr; forward;
  function mDIV ( x, y : TExpr ) : TExpr; forward;
  function mMOD ( x, y : TExpr ) : TExpr; forward;
  function mPOW ( x, y : TExpr ) : TExpr; forward;

  function mREADFILE  ( path : TExpr ) : TExpr; forward;
  function mWRITEFILE ( path, data : TExpr ) : TExpr; forward;
  function mBINREAD   ( path : TExpr ) : TExpr; forward;
  function mBINWRITE  ( path, data : TExpr ) : TExpr; forward;
  function mARRAY     ( size : TExpr ) : TExpr; forward;
  function mLEN       ( a : TExpr ) : TExpr; forward;
  function mPUSH      ( a, x : TExpr ) : TExpr; forward;
  function mPOP       ( a, x : TExpr ) : TExpr; forward;
  function mSYM2CHARS ( x : TExpr ) : TExpr; forward;
  function mCHARS2SYM ( chars : TExpr ) : TExpr; forward;
{ }{$ENDIF}

// We will also need a routine to bind names to their values at runtime,
// but we'll postpone defining it until after we've defined mEVAL.
// Also, we will want to experiment with various representations for
// storing variable names and their bindings. Therefore, instead of
// simply declaring this as a 'forward' function, we'll create a
// global function variable:
var bindFn : TMetaFun2; // (identifier, value)->identifier

// Now we can define a function to create a symbol from a pascal
// string and bind it to a value.
function Define(iden:string; value:TExpr) : TExpr;
  begin
    result := bindFn(Sym(iden), value)
  end;

// It would be nice if we could also pass in the function pointer
// above, but that would require duplicating the type-system
// shenannigans we already went through when we defined Meta().
// So... The following function is a bit long and tedious, but
// also very simple. (This is exactly the sort of place where a
// meta-programming system would come in handy. But since we're
// still building it, we just have to do the work.)
procedure CreateBuiltins;
  begin
    sAtomP := Define('atom?', Meta(@mATOMP));
    sEqP := Define('eq?', Meta(@mEQP));
    sCar := Define('car', Meta(@mCAR));
    sCdr := Define('cdr', Meta(@mCDR));
    sCons := Define('cons', Meta(@mCONS));
    sSubst := Define('subst', Meta(@mSUBST));
    sEqualP := Define('equal', Meta(@mEQUAL));
    sNullP := Define('null?', Meta(@mNULLP));
    sCaar := Define('caar', Meta(@mCAAR));
    sCadr := Define('cadr', Meta(@mCADR));
    sCadar := Define('cadar', Meta(@mCADAR));
    sCaddr := Define('caddr', Meta(@mCADDR));
    sAppend := Define('append', Meta(@mAPPEND));
    sAmongP := Define('among?', Meta(@mAMONGP));
    sZip := Define('zip', Meta(@mZIP));
    sAssoc := Define('assoc', Meta(@mASSOC));
    sSublis := Define('sublis', Meta(@mSUBLIS));
    sApply := Define('apply', Meta(@mAPPLY));
    sEval := Define('eval', Meta(@mEVAL));
    sAppq := Define('appq', Meta(@mAPPQ));
    sList := Define('list', Meta(@mLIST));
    sMapList := Define('maplist', Meta(@mMAPLIST));
    sSearch := Define('search', Meta(@mSEARCH));
    sFilter := Define('filter', Meta(@mFILTER));
    sReduce := Define('reduce', Meta(@mREDUCE));
    sAdd := Define('+', Meta(@mADD));
    sSub := Define('-', Meta(@mSUB));
    sMul := Define('*', Meta(@mMUL));
    sDiv := Define('%', Meta(@mDIV));
    sMod := Define('|', Meta(@mMOD));
    sPow := Define('**', Meta(@mPOW));
    sReadFile := Define('read-file', Meta(@mREADFILE));
    sWriteFile := Define('write-file', Meta(@mWRITEFILE));
    sBinRead := Define('bin-read', Meta(@mBINREAD));
    sBinWrite := Define('bin-write', Meta(@mBINWRITE));
    sArray := Define('array', Meta(@mARRAY));
    sLen := Define('len', Meta(@mLEN));
    sPush := Define('push', Meta(@mPUSH));
    sPop := Define('pop', Meta(@mPOP));
    sSym2Chars := Define('sym->chars', Meta(@mSYM2CHARS));
    sChars2Sym := Define('chars->sym', Meta(@mCHARS2SYM));
  end;


// This next part is here both to provide some docs and to
// suppress the 'variable assigned but never used' notes...
procedure Doc(sym : TExpr; s : string );
  begin
    //  TODO! AddHelp(...)
  end;

procedure DescribeBuiltins;
  begin
    Doc(sAtomP , '(sym -> bool) is symbol an atom?');
    Doc(sEqP, '(x y -> bool) are symbols x and y the same?');
    Doc(sCar, '(x.y -> x) first item in list (or: left side of cell)');
    Doc(sCdr, '(x.y -> y) list w/o first item (or: right side of cell)');
    Doc(sCons, '(x y -> x.y) construct a cell from x and y');
    Doc(sSubst, '(x y zz -> zz'') zz with each y replaced by x.');
    Doc(sEqualP, '(xx yy -> bool) are the two lists equal?');
    Doc(sNullP, '(x -> boolean) is x null?');
    Doc(sCaar, '((x.y).z) -> x');
    Doc(sCadr, '(x.(y.z)) -> y');
    Doc(sCadar, '((w.(x.y)).z) -> x');
    Doc(sCaddr, '(w.(x.(y.z))) -> y');
    Doc(sAppend, 'xx yy -> xxyy | create a copy of xx with yy appended');
    Doc(sAmongP, 'list x -> bool | is x in the list?');
    Doc(sZip, 'xx yy -> x0y0 x1y1.. | list of list of paired members');
    Doc(sAssoc, 'k a -> v | value for key in a = ((k0,v0) (k1,v1) ...)');
    Doc(sSublis, 'x y -> subst uN->vN in y; x=((u0,v0), (u1,v1)...)');
    Doc(sApply, 'f args -> f(args)');
    Doc(sEval, 'evaluate the given expression');
    Doc(sAppq, 'xyz -> ''x ''y ''z | quote each item in the list');
    Doc(sList, 'evaluate each argument and return a list of the results');
    Doc(sMapList, 'TODO');
    Doc(sSearch, 'TODO');
    Doc(sFilter, 'TODO');
    Doc(sReduce, 'TODO');
    Doc(sAdd, 'x y -> x + y');
    Doc(sSub, 'x y -> x - y');
    Doc(sMul, 'x y -> x * y');
    Doc(sDiv, 'x y -> x div y');
    Doc(sMod, 'x y -> x mod y');
    Doc(sPOW, 'x y -> x ** y');
    Doc(sReadFile, 'path -> list | read file as list of expressions');
    Doc(sWriteFile, 'path list -> | write list to file');
    Doc(sBinRead, 'path -> array | read array of bytes');
    Doc(sBinWrite, 'path array -> | write array to file as bytes');
    Doc(sArray, 'length -> array | create a new array');
    Doc(sLen, 'array -> int | length of the array');
    Doc(sPush, 'array int -> int | add item end of the array');
    Doc(sPop, 'array -> int | remove last item from the array');
    Doc(sSym2Chars, 'sym -> [char] | symbol as list of characters');
    Doc(sChars2Sym, '[char] -> sym | symbol from given characters');
  end;

// That's it for rule 2 for meta->symbolic translation.
// The others won't require nearly as much work.


// 3. A form  f[e1; ...; en*] is translated to  (f*, e1* ... en*).
// Thus cons [car [x]; cdr [x]]* is (CONS (CAR X) (CDR X)).
//
// For us, we map from functions to lists, so our translation is:
// mCONS(mCAR(x), mCDR(x)) -> L(sCons, L(sCar, x), L(sCdr, x));
//
// That's just an application of what we've already created.
// While we're here though, we want implish to support a few things
// that the original lisp didn't have. Most importantly: numbers,
// strings, and perhaps even arrays.
//
// The functions Vx(value) (for 'variant expression') and
// VL([v0,v1,v2...]) provides a syntax for building TExpr
// values from pascal variants:
//
// usage: Vx(3) -> Sx(kINT, 3)
// usage: VL([3]) -> L(Sx(kINT, 3))
//

{ }{$IFDEF IMPSHELL}
// forward ref because they can call each other recursively.
{ }function VL(vars : array of variant) : TExpr; forward;
{ }{$ENDIF}

function Vx(v : variant) : TExpr; overload;
  begin
    case VarType(v) and VarTypeMask of
      varEmpty,
      varNULL : result := sNULL;

      varSmallInt,
      varShortInt,
      varByte,
      varWord,
      varInteger : result := Sx(kINT, v);
      // varSingle
      // varDouble
      // varCurrency
      // varDate
      // varDispatch
      // varError
      varBoolean : result := EnBool(v);
      // varVariant
      // varUnknown
      // varLongWord
      // varInt64
      varOleStr, varStrArg, varString:
        result := Sym(v);
      // varAny: ;
      // varTypeMask : ;
    else result :=
      Sx(kERR, Key(
           '<|type:' + VarTypeAsText(VarType(v))
           +'|:"' + VartoStr(v)
           +'">'));
    end
  end;

function VL(vars : array of variant) : TExpr;
  var i: integer;
  begin
    result := sNULL;
    for i := high(vars) downto 0 do
      result := mCONS(Vx(vars[i]), result)
  end; { VL }

// e4. Cond
// e5. Lambda
// e6. Label
//
// See note above (in e1. Quote).

//-- f. universal evaluator ------------------------------------

function mAPPQ( m : TExpr ) : TExpr;
  begin
    if mNULL(m) then result := sNULL
    else result := mCONS(q(mCAR(m)), mAPPQ(mCDR(m)))
  end;

function mAPPLY( f, args, env : TExpr ) : TExpr;
  begin
    result := mEVAL(mCONS(f, mAPPQ(args)), env)
  end;

function mEVAL( e, a : TExpr ) : TExpr;

  function mEVCON( c, a : TExpr ) : TExpr;
    begin
      if exBool(mEVAL(mCAAR(c), a))
        then result := mEVAL(mCADAR(c), a)
        else result := mEVCON(mCDR(c), a)
    end; { mEVCON }

  function mEVLIS( m, a : TExpr ) : TExpr;
    begin
      if mNULL(m) then result := sNULL
      else result := mCONS(mEVAL(mCAR(m), a), mEVLIS(mCDR(m), a))
    end; { mEVLIS }

  var
    h{head}, r{result}, x : TExpr;
  begin { mEVAL }
    if mATOM(e) then
      if e.kind = kSYM then r := mASSOC(e, a)
      else r := e
    else if mATOM(mCAR(e)) then
      begin
        h := mCAR(e);
        { eval[(QUOTE X), a] -> X # 1 argument only }
        if mEQ(h, sQUOTE) then r := mCADR(e)

        else if mEQ(h, sENV) then r := a
        else if mEQ(h, sDEF) then r := bindFn(mCADR(e), mCADDR(e))

        { eval[(ATOM? X), a] -> atom?[eval[X]] }
        else if mEQ(h, sATOMP) then r := mATOMP(mEVAL(mCADR(e), a))
        { eval[(EQ? X Y), a] -> eq?[eval[X,a] eval[Y,a]] }
        else if mEQ(h, sEQP) then r := mEQP(mEVAL(mCADR(e), a),
                                            mEVAL(mCADDR(e), a))
        { eval[(COND h|t), a] -> evcon[h|t, a] }
        else if mEQ(h, sCOND) then r := mEVCON(mCDR(e), a)
        { eval[(CAR X), a] -> car[eval[X, a]] }
        else if mEQ(h, sCAR) then r := mCAR(mEVAL(mCADR(e), a))
        { eval[(CDR X), a] -> cdr[eval[X, a]] }
        else if mEQ(h, sCDR) then r := mCDR(mEVAL(mCADR(e), a))
        { eval[(CONS X Y), a] -> cons[eval[X, a], eval[Y, a]] }
        else if mEQ(h, sCONS) then r := mCONS(mEVAL(mCADR(e), a),
                                              mEVAL(mCADDR(e), a))
        { eval[h|t, a] -> eval[cons[eval[h,a], evlis[t, a]], a] }
        else begin
          x := mASSOC(h, a);
          case x.kind of
            kERR : r := x;
            kMF0 : r := metas[x.data].f0();
            kMF1 : r := metas[x.data].f1(mEVAL(mCADR(e), a));
            kMF2 : r := metas[x.data].f2(mEVAL(mCADR(e), a),
                                         mEVAL(mCADDR(e), a));
            kMF3 : r := metas[x.data].f3(mEVAL(mCADR(e), a),
                                         mEVAL(mCADDR(e), a),
                                         mEVAL(mCADDDR(e), a));
            kMF4 : r := metas[x.data].f4(mEVAL(mCADR(e), a),
                                         mEVAL(mCADDR(e), a),
                                         mEVAL(mCADDDR(e), a),
                                         mEVAL(mCADDDDR(e), a));
            else r := mEVAL(mCONS(x, mEVLIS(mCDR(e), a)), a)
          end
        end
      end
    { eval[((LABEL X Y) Z), a] -> eval[cons[Y Z], cons[(X Y), a]] }
    else if mEQ(mCAAR(e), sLABEL) then
      r := mEVAL(mCONS(mCADDAR(e), mCDR(e)),
                 mCONS(L(mCADAR(e), mCAR(e)), a))
    { eval[((LAMBDA X Y) Zz),a] -> eval[Y, append[zip[X, evlis[Zz]],a]] }
    else if mEQ(mCAAR(e), sLAMBDA) then
      r := mEVAL(mCADDAR(e),
                 mAPPEND(mZIP(mCADAR(e),
                              mEVLIS(mCDR(e), a)), a));
    result := r
  end; { mEVAL }

{$IFDEF IMPSHELL}
var mENV : TExpr; // initial environment
{$ENDIF}
function mBIND( iden, value : TExpr ) : TExpr;
  begin
    mENV := mCONS(L(iden, value), mENV); // flat list of pairs for now
    result := iden;
  end;

function mLIST ( x : TExpr ) : TExpr;
  begin
    result := sNULL
  end;

//-- g. higher order functions ---------------------------------

function mMAPLIST( f, x : TExpr ) : TExpr;
  begin
    result := sNULL
  end;

function mSEARCH( f, x : TExpr ) : TExpr;
  begin
    result := sNULL
  end;

function mFILTER( f, x : TExpr ) : TExpr;
  begin
    result := sNULL
  end;

function mREDUCE( f, x, y : TExpr ) : TExpr;
  begin
    result := sNULL
  end;

//-- arithmetic  -----------------------------------------------

function ints( x, y : TExpr; out errx : TExpr) : boolean;
  begin
    result := (x.kind = kINT) and (y.kind = kINT);
    if not result then errx := Err('NaN');
  end; { ints }

function Nx( n : integer ) : TExpr;
  begin
    result := Sx(kINT, n)
  end;

function mADD( x, y : TExpr ) : TExpr;
  begin
    if ints(x,y,result) then result := Nx(x.data + y.data)
  end;

function mSUB( x, y : TExpr ) : TExpr;
  begin
    if ints(x,y,result) then result := Nx(x.data - y.data)
  end;

function mMUL( x, y : TExpr ) : TExpr;
  begin
    if ints(x,y,result) then result := Nx(x.data * y.data)
  end;

function mDIV( x, y : TExpr ) : TExpr;
  begin
    if ints(x,y,result) then result := Nx(x.data div y.data)
  end;

function mMOD( x, y : TExpr ) : TExpr;
  begin
    if ints(x,y,result) then result := Nx(x.data mod y.data)
  end;

function mPOW( x, y : TExpr ) : TExpr;
  begin
    if ints(x,y,result) then result := Nx(x.data ** y.data)
  end;

// - functions - - - - - - - - - - - - - - - - - - - - - - - - -
type
  TBind = record // name bindings.
    iden : integer; // index of a string
    cell : TCell;   // car=value cdr=attributes
  end;
  TDefTbl = specialize arrays.GArray<TBind>;

var
  defs : TDefTbl;
const
  whitespace  = [#0..' '];
  stopchars   = whitespace + ['(',')','[',']','{','}', '"', ''''];
  commentChar = '#';
  prompt0     = 'imp> ';
  prompt1     = '...> ';

type
  TFormat = (fmtLisp, fmtStruct);
var
  debugging : boolean = true;
  ShowFormat : TFormat = fmtLisp;

function k2s( kind :  TKind ) : string;
  begin
    case kind of
      kNUL : result := 'NUL';
      kCEL : result := 'CEL';
      kERR : result := 'ERR';
      kINT : result := 'INT';
      kSTR : result := 'STR';
      kMF1 : result := 'MF1';
      kMF2 : result := 'MF2';
      kMF3 : result := 'MF3';
      kMF4 : result := 'MF4';
    end
  end;

procedure debug( msg : string ); inline;
  begin
    if debugging then writeln( msg )
  end;

//== read part =================================================
{$IFDEF IMPSHELL}
type
  TStrGen = function(out s : string) : boolean is nested;
  TImplishReader = class
  private
    ch	 : char;
    line : string;
    nest : string;
    atEOF : boolean;
    lx, ly : cardinal;
    getLine : TStrGen;
    procedure SyntaxError(const err : string);
    function  Depth : cardinal;
    function NextChar(var _ch :  char ) : char;
    function IsNum( s : string; out num : integer ) : boolean;
    function ReadAtom : TExpr;
    function ReadString : TExpr;
    procedure HandleDirective;
    procedure SkipCommentsAndWhitespace;
    function ReadListEnd : TExpr;
  public
    constructor Create( gen : TStrGen );
    function NextExpr( out value : TExpr ): TExpr;
  end;
{$ENDIF}

constructor TImplishReader.Create( gen : TStrGen );
  begin
    ch :=  #0; nest := ''; getLine := gen; atEOF := false;
  end; { TImplishReader.Create }

procedure TImplishReader.SyntaxError( const err: string );
  begin
    writeln( '=== syntax error at line ', ly, ', column ', lx, ': ===' );
    halt( err );
  end; { TImplishReader.SyntaxError }

function TImplishReader.Depth : cardinal;
  begin
    result := Length(nest);
  end; { TImplishReader.Depth }

  var ps : string; // TODO: clean this prompt mess up!!
function prompt( out line : string ) : boolean;
  begin
    result := true;
    {$IFDEF NOPROMPT}
    if eof then result := false;
    else begin readln(line);
    {$ELSE}
      if lined.prompt(ps, line) then begin
    {$ENDIF}
	writeln;
	line := line + ascii.LF; { so we can do proper lookahead. }
      end
    {$IFNDEF NOPROMPT}else
        begin
	  result := false;
	  system.halt;
	end
    {$ENDIF}
  end;

type EndOfFile = class (Exception) end;
function TImplishReader.NextChar( var _ch : char ) : char;
  begin
    result := #0;
    while lx + 1 > length( line ) do begin
      if self.atEOF then raise EndOfFile.Create('');
      {$IFDEF NOPROMPT}
      ps := '';
      {$NOTE compiling without prompt}
      {$ELSE}
      if depth > 0
        then ps := nest + prompt1
        else ps := prompt0;
      {$ENDIF}
      if self.getLine(self.line) then
	begin
	  lx := 0; inc(ly);
	  AppendStr(self.line, ascii.lf);
	end
      else self.atEOF := true
    end;
    inc( lx );
    result := self.line[ lx ];
    // debug( '[ line ' + n2s( ly ) +
    //       ', column ' + n2s( lx ) + ' : ' +  result + ']' );
    _ch := result;
  end; { TImplishReader.NextChar }

// this recognizes decimal integers.
function TImplishReader.IsNum( s : string; out num : integer ) : boolean;
  var i : cardinal = 1; negate : boolean = false;
  begin
    result := true; num := 0;
    if (s[1] = '-') and (length(s) > 1) then
      begin inc(i); negate := true; end;
    while result and (i <= length(s)) do begin
      if s[i] in ['0'..'9'] then num := num * 10 + ord(s[i]) - ord('0')
      else result := false;
      Inc(i);
    end;
    if result and negate then num := -num;
  end; { TImplishReader.IsNum }

function TImplishReader.ReadAtom : TExpr;
  var tok : string = ''; i : integer;
  begin
    repeat tok := tok + ch until NextChar(ch) in stopchars;
    if IsNum( tok, i )
      then result := Sx( kINT, i )
      else result := Sx( kSYM, Key( tok ))
  end; { TImplishReader.ReadAtom }

function PopChar( var s : string ) : char;
  var last : integer; ch : char;
  begin
    last := Length(s);
    if last = 0 then ch := #0 else ch := s[ last ];
    SetLength( s, last - 1 );
    result := ch;
  end; { PopChar }

function TImplishReader.ReadString : TExpr;
  var s : string = '';
  begin
    AppendStr(nest, '"');
    while NextChar(ch) <> '"' do
      if ch = '\' then
        case NextChar(ch) of
          '0' : s := s + #0;
          't' : s := s + ^I;
          'n' : s := s + LineEnding;
          else s := s + ch;
        end
      else s := s + ch;
    PopChar(nest); NextChar(ch);
    result := Sx(kSTR, Key(s))
  end; { TImplishReader.ReadString }

procedure TImplishReader.HandleDirective;
  var s : string = '';
  begin
    while ch <> ascii.LF do s += NextChar(ch);
    if AnsiStartsStr('fmt:struct', s) then showFormat := fmtStruct;
  end; { TImplishReader.HandleDirective }

procedure TImplishReader.SkipCommentsAndWhitespace;
  begin
    //writeln('1: ord(ch):', ord(ch), '... atEOF: ', atEOF);
    while (ch in whitespace) and not atEOF do begin
      if NextChar(ch) = commentChar then
        if NextChar(ch) = '%' then HandleDirective
	else while (ch <> ascii.LF) and not atEOF do
          begin
	    //writeln('2: ord(ch):', ord(ch), '... atEOF?', atEOF);
	    NextChar(ch);
	  end;
    end
  end; { TImplishReader.SkipCommentsAndWhitespace }

function TImplishReader.ReadListEnd : TExpr;
  var expect : char;
  begin
    if depth = 0 then result := Err('Unexpected char: ' + ch)
    else begin
      case PopChar(nest) of
        '{' : expect := '}';
        '[' : expect := ']';
        '(' : expect := ')';
        else expect := '?' // should never happen
      end;
      if ch = expect then result := sNULL
      else result := Err('List end mismatch. Expected: '
			 + expect + ', got: ' + ch);
    end;
    NextChar(ch);
  end; { TImplishReader.ReadListEnd }

function TImplishReader.NextExpr( out value : TExpr ): TExpr;

  function ReadList( out res : TExpr; AtHead : boolean) : TExpr;
    var car, cdr : TExpr;
    begin
      if AtHead then begin nest += ch; NextChar(ch) end;
      SkipCommentsAndWhitespace;
      if (ch in [')', ']', '}']) then
        begin
          res := sNULL; NextChar(ch);
        end
      else if NextExpr(car).kind = kERR then res := car
      else if ReadList(cdr, false).kind = kERR then res := cdr
      else res := MCons(car, cdr);
      if AtHead then PopChar(nest);
      result := res;
      // debug('List -> ' + k2s(res.kind) + ' : ' + ShowExpr(res));
    end; { ReadList }

  function ReadQuote : TExpr;
    begin
      NextChar(ch);
      if NextExpr(result).kind <> kERR
      then result := q(result)
    end; { ReadQuote }

  begin
    try
      //if atEOF then raise EndOfFile.Create('');
      //writeln('skipping comments...');
      SkipCommentsAndWhitespace;
      //writeln('reading. ch=', ch);
      case ch of
	'(','[','{' : ReadList(result, true);
	')',']','}' : result := ReadListEnd;
	'"'	    : result := ReadString;
	''''	    : result := ReadQuote;
	else result := ReadAtom;
      end
    except
      on EndOfFile do
	if depth > 0 then result := Err('unexpected end of file!')
	else result := Sx(kEOF, 0)
    end;
    value := result;
  end; { TImplishReader.NextExpr }

//== eval part =================================================
// The evaluator applies functions that are in the car of a cell
// to that same cell's cdr.

procedure Def( strid : cardinal; expr : TExpr );
  var binding : TBind;
  begin
    binding.iden := strid;
    binding.cell.car := expr;
    defs.Append( binding );
  end;

function FQuote( var expr : TExpr ) : TExpr;
  begin
    result := expr
  end;

function Eval( itm : TExpr ) : TExpr;
  begin
    result := mEVAL(itm, mENV)
  end;

//== print part ================================================

function DumpCell( ref : TExpr ): string;
  var cell : TCell;
  begin
    cell := cells[ ref.data ];
    result :=
      'Cons(' +
      k2s(cell.car.kind) + ':' + n2s(cell.car.data) + ',' +
      k2s(cell.cdr.kind) + ':' + n2s(cell.cdr.data) + '):' +
      n2s(ref.data);
  end; { DumpCell }

function ShowExpr( expr : TExpr ) : string;

  function ShowList( ref : TExpr; AtHead : boolean) : string;
    var cell : TCell;
    begin
      // debug('ShowList:' + DumpCell(ref));
      if AtHead then result := '(' else result := ' ';
      cell := cells[ ref.data ];
      result += ShowExpr( cell.car );
      if showFormat = fmtStruct then
        AppendStr( result, ' . ' + ShowExpr( cell.cdr ) + ')')
      else case cell.cdr.kind of
        kNUL : AppendStr( result, ')' );
        kCEL : AppendStr( result, ShowList( cell.cdr, false ));
        else   AppendStr( result, ' . ' + ShowExpr( cell.cdr ) + ')');
      end;
    end; { ShowList }

  begin
    case expr.kind of
      KNUL,
      kERR,
      kSYM : result := syms[ expr.data ];
      kSTR : result := '"' + syms[ expr.data ] + '"';
      kINT : result := IntToStr( expr.data );
      kCEL : result := ShowList( expr, true );
      else result := '<' + IntToStr( expr.data ) + '>';
    end;
    if showFormat = fmtStruct then
      case expr.kind of
        KNUL,
        kERR,
        kSYM,
        kSTR : result := 's:' + result;
        kINT : result := 'n:' + result;
        kCEL : result := ShowList( expr, true );
        else result := 'm:' + result;
      end;
  end; { ShowExpr }

procedure Print( expr : TExpr );
  begin
    WriteLn(ShowExpr(expr));
  end;

procedure Shell;
  var val : TExpr; reader : TImplishReader;
  begin
    reader := TImplishReader.Create(@prompt);
    repeat Print(Eval(reader.NextExpr(val)))
    until val.kind in [kERR, kEOF];
    reader.Free;
  end;

{-- support routines for parser stuff --}

type TExprStack = specialize GStack<TExpr>;

function ReadFile( path : string ) : TExpr;
  var
    f  : text;
    r  : TImplishReader;
    x  : TExpr;
    xs : TExprStack;
  function NextLine( out line : string ): boolean;
    begin
      if Eof(f) then result := false
      else begin
	result := true;
	ReadLn(f, line);
	// write('nextline: "', line);
      end;
      // if not result then raise Exception.Create('for stack trace');
    end;
  begin
    Assign(f, path); Reset(f);
    r := TImplishReader.Create( @NextLine );
    xs := TExprStack.Create(1024);
    while not (r.NextExpr( x ).kind in [kERR, kEOF]) do begin
      // debug('expr from file: ' + ShowExpr(x));
      xs.push(x);
    end;
    if x.kind = kERR then result := x
    else begin
      result := sNULL;
      while xs.count > 0 do begin
	result := mCONS( xs.pop, result );
      end;
    end;
    xs.Free;
    r.Free;
    CloseFile(f);
    // debug('ReadFile result:' + ShowExpr(result));
  end; { ReadFile }

function mREADFILE  ( path : TExpr ) : TExpr;
  begin
    if path.kind in [kSYM, kSTR]
      then result := ReadFile(syms[path.data])
      else result := Err('READFILE: expected filename, got: '
			 + ShowExpr(path))
  end; { mREADFILE }

function mWRITEFILE ( path, data : TExpr ) : TExpr;
  begin
    result := sNULL
  end; { mWRITEFILE }

function mBINREAD   ( path : TExpr ) : TExpr;
  begin
    result := sNULL
  end; { mBINREAD }

function mBINWRITE  ( path, data : TExpr ) : TExpr;
  begin
    result := sNULL
  end; { mBINWRITE }

function mARRAY ( size : TExpr ) : TExpr;
  begin
    result := sNULL
  end; { mARRAY }

function mLEN ( a : TExpr ) : TExpr;
  begin
    result := sNULL
  end; { mLEN }

function mPUSH ( a, x : TExpr ) : TExpr;
  begin
    result := sNULL
  end; { mPUSH }

function mPOP ( a, x : TExpr ) : TExpr;
  begin
    result := sNULL
  end; { mPOP }

// ! sym2chars is almost exactly the same as VL()
// ... worth it to consolidate with a template / generic?
function mSYM2CHARS ( x : TExpr ) : TExpr;
  var i : cardinal; s : string;
  begin
    if x.kind = kERR then result := x
    else if x.kind in [kSTR, kSYM] then
      begin
        result := sNULL; s := syms[x.data];
	for i := length(s) downto 1 do
	  result := mCONS(Sym(s[i]), result)
      end
    else result := Err('sym->chars: expected symbol, got ' +
		       k2s(x.kind))
  end; { mSYM2CHARS }

function mCHARS2SYM ( chars : TExpr ) : TExpr;
  begin
    result := sNULL
  end; { mCHARS2SYM }

begin
  syms := TSymTbl.Create;
  cells := TCellTbl.Create;
  defs := TDefTbl.Create;
  bindFn := @mBIND;
  CreateBooleans;
  mENV := L(L(sTRUE, sTRUE)); // bind #t to itself
  CreateBuiltins;
  CreateSpecials;
{ }{$IFDEF IMPSHELL}
  Shell;
{ }{$ENDIF}
end.
