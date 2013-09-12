//--------------------------------------------------------------
// implish: an imperative meta-programming language.
//
// Copyright 2013 Michal J Wallace <http://tangentstorm.com/>
// Avaliable to the public for use under the MIT/X11 License.
//--------------------------------------------------------------
{$mode objfpc}{$i xpc.inc}
program imp(input, output);
uses xpc, arrays, stacks, ascii, sysutils, strutils, num;

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
type
  TKind = (
    kSYM,  // an symbol or 'atom', represented internally by a string
    kNUL,  // NULL, a special symbol. Represents false and the empty list.
    kERR,  // used to mark represent error conditions
    kSTR,  // alternate symbol syntax with quotes to allow spaces
    kINT,  // an integer
    kCEL,  // a 'cons cell' (pair of sybols)
    kMF1,  // a meta-function (a:TExpr -> TExpr, implemented in pascal)
    kMF2,  // a meta-function (a,b:TExpr -> TExpr)
    kMF3,  // a meta-function (a,b,c:TExpr -> TExpr)
    kMF4); // a meta-function (a,b,c,d:TExpr -> TExpr)

  TExpr = record
            kind : TKind;
            data : integer;
          end;

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
type
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
  TMetaTbl = array [byte] of pointer;
var
  metas	    : TMetaTbl;
  metacount : byte = 0;

// Meta adds a function record to the 'metas' table and constructs
// a unique symbol for it.
function NextMeta( k : TKind; p : pointer ) : TExpr;
  begin
    metas[metacount] := p;
    if metacount > high(metas) then halt( 'out of meta slots.' );
    result := Sx(k, metacount);
    inc(metacount);
  end;

function Meta( f : TMetaFun1 ) : TExpr; overload;
  begin NextMeta(kMF1, @f) end;

function Meta( f : TMetaFun2 ) : TExpr; overload;
  begin NextMeta(kMF2, @f) end;

function Meta( f : TMetaFun3 ) : TExpr; overload;
  begin NextMeta(kMF3, @f) end;

function Meta( f : TMetaFun4 ) : TExpr; overload;
  begin NextMeta(kMF4, @f) end;

//-- c. elementary meta-expressions ----------------------------

// These are the elementary expressions from the 1960 LISP paper.
//
// The M prefix used in these routines is short for 'meta', since
// we're using pascal as a meta-language to describe lisp. As a
// convention, we will also type meta function names in ALL CAPS.

// 1. atom[x] -> T if x is an atom, else F
function MATOM( x : TExpr ) : boolean;
  begin
    result := x.kind in atomic
  end; { MATOM }

// 2. eq[x;y] = atom[x] ? atom[y] ? x = y | F | undefined
// We'll just treat the undefined case as false.
function MEQ( x, y : TExpr ) : boolean;
  begin
    result := MATOM(x) and MATOM(y)
      and (x.kind = y.kind)
      and (x.data = y.data)
  end; { MEQ }

// 3. car[x] = atom[x] ? undefined | x0 where x = (x0, x1)
// We'll use an error symbol for the undefined case.
function MCAR( x : TExpr ) : TExpr;
  begin
    if MATOM(x) then result := Sx(kErr, Key('!CAR[atom]'))
    else result := cells[x.data].car
  end; { MCAR }

// 4. cdr[x] = atom[x] ? undefined | x1 where x = (x0, x1)
function MCDR( x : TExpr ) : TExpr;
  begin
    if MATOM(x) then result := Sx(kErr, Key('!CDR[atom]'))
    else result := cells[x.data].cdr
  end; { MCdr }

// 5. cons[x;y] -> (x, y)
function MCONS( x, y : TExpr ) : TExpr;
  var cell : TCell;
  begin
    cell.car := x;
    cell.cdr := y;
    result := Sx( kCEL, cells.Append( cell ));
  end; { MCons }

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

var { boolean symbols }
  sNULL : TExpr;
  sTRUE : TExpr;

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

// We can now define new versions of MATOM and MEQ as TExpr->TExpr.
// Following lisp tradiion, the P suffix is used both as an
// abbreviation for the word 'predicate' and for its resemblence
// to a question mark.

function MATOMP( x : TExpr ) : TExpr;
  begin
    result := EnBool( MATOM( x ))
  end;

function MEQP( x, y : TExpr ) : TExpr;
  begin
    result := EnBool( MEQ( x, y ))
  end;

//-- d. recursive meta-functions -------------------------------

// 1. ff[x] -> first atomic symbol in f, ignoring parentheses.
// Perhaps this is an abbreviation for "find first".
function MFF( x : TExpr ) : TExpr;
  begin
    if MATOM(x) then result := x else result := MFF(MCAR(x))
  end;

// 2. subst[x;y;z] -> copy z, replacing each occurrence of y with x.
function MSUBST( x, y, z : TExpr ) : TExpr;
  begin
    if MATOM(z) then
      if MEQ(z, y) then result := x
      else result := z
    else result := MCONS(MSUBST(x, y, MCAR(z)),
                         MSUBST(x, y, MCDR(z)))
  end;

// 3. equal[x;y] -> T if x and y are the same, else F
function MEQUAL( x, y : TExpr ) : TExpr;
  begin
    result := EnBool(
      ( MATOM(x) and MATOM(y) and MEQ(x, y) )
      or ( not ( MATOM(x) or MATOM(y) )
           and MEQ(MCAR(x), MCAR(y))
           and MEQ(MCDR(x), MCDR(y)) ) )
  end;

// 4. null?(x) -> T if x = NIL else F
function MNULL( x : TExpr ) : boolean;
  begin
    result := MEQ(x, sNULL)
  end;

// here is the reified version:
function MNULLP( x : TExpr ) : TExpr;
  begin
    result := MEQP(x, sNULL)
  end;

// - abbreviations - - - - - - - - - - - - - - - - - - - - - - -

// caar[x] -> car[car[x]]
function MCAAR( x : TExpr ) : TExpr;
  begin
    result := MCAR(MCAR(x))
  end;

// cadr[x] -> car[cdr[x]]
function MCADR( x : TExpr ) : TExpr;
  begin
    result := MCAR(MCDR(x))
  end;

// cadar[x] -> car[cdr[cdr[x]]]
function MCADAR( x : TExpr ) : TExpr;
  begin
    result := MCAR(MCDR(MCAR(x)))
  end;

// caddr[x] -> car[cdr[cdr[x]]]
function MCADDR( x : TExpr ) : TExpr;
  begin
    result := MCAR(MCDR(MCDR(x)))
  end;

// - list builder - - - - - - - - - - - - - - - - - - - - - - - -
// We'll define MLIST for up to 10 items, as a convenience for
// people writing meta-extensions in pascal.

function MLIST( a : TExpr ) : TExpr;
  begin result := MCONS(a, sNULL) end;

// After the first version, each successive version can simply
// CONS its first argument onto the MLIST of the other arguments.

// Note that MLIST with two arguments is *NOT* the same as MCONS.
// (cons a (b c)) -> (a b c)
// (list a (b c)) -> (a (b c))
function MLIST( a, b : TExpr ) : TExpr; inline;
 begin result := MCONS(a, MLIST(b)) end;

function MLIST( a, b, c : TExpr ) : TExpr; inline;
  begin result := MCONS(a, MLIST(b, c)) end;

function MLIST( a, b, c, d : TExpr ) : TExpr; inline;
  begin result := MCONS(a, MLIST(b, c, d)) end;

function MLIST( a, b, c, d, e : TExpr ) : TExpr; inline;
  begin result := MCONS(a, MLIST(b, c, d, e)) end;

function MLIST( a, b, c, d, e, f : TExpr ) : TExpr; inline;
  begin result := MCONS(a, MLIST(b, c, d, e, f)) end;

function MLIST( a, b, c, d, e, f, g : TExpr ) : TExpr; inline;
  begin result := MCONS(a, MLIST(b, c, d, e, f, g)) end;

function MLIST( a, b, c, d, e, f, g, h : TExpr ) : TExpr; inline;
  begin result := MCONS(a, MLIST(b, c, d, e, f, g, h)) end;

function MLIST( a, b, c, d, e, f, g, h, i : TExpr ) : TExpr; inline;
  begin result := MCONS(a, MLIST(b, c, d, e, f, g, h, i)) end;

function MLIST( a, b, c, d, e, f, g, h, i, j : TExpr ) : TExpr; inline;
  begin result := MCONS(a, MLIST(b, c, d, e, f, g, h, i, j)) end;

// - functions - - - - - - - - - - - - - - - - - - - - - - - - -

// append[x;y] -> append y to x
function MAPPEND( x, y : TExpr ) : TExpr;
  begin
    if MNULL(x) then result := MLIST(x)
    else result := MCONS(MCAR(x), MAPPEND(MCDR(x), y))
  end;

// among [x;y] = ~null[y] ^ [equal [x;car [y]] | among [x;cdr[y]]]
// is x in list y?
function MAMONG( x, y : TExpr ) : boolean;
  begin
    result := MEQ(x,MCAR(y)) or MAMONG(x, MCDR(y))
  end;

function MAMONGP( x, y : TExpr ) : TExpr;
  begin
    result := EnBool(MAMONG(x, y))
  end;

// zip -- McCarthy calls this 'pair'. 'zip' comes from haskell and python.
function MZIP( x, y : TExpr ) : TExpr;
  begin
    if MATOM(x) or MATOM(y) then result := sNULL
    else result := MCONS(MLIST(MCAR(x), MCAR(y)),
                         MZIP(MCDR(x), MCDR(y)))
  end;

// assoc[x;y] look up x in dictionary y
function MASSOC( x, y : TExpr ) : TExpr;
  begin
    if MEQ(MCAAR(y), x) then result := MCADAR(y)
    else result := MASSOC(x, MCDR(y))
  end;

// sublis[x;y] -> subst uN->vN in y, where x=((u0,v0), (u1,v1)...)
function MSUBLIS( x, y : TExpr ) : TExpr;
  function SUB2( x, z : TExpr ) : TExpr;
    begin
      if MNULL(x) then result := z
      else if MEQ(MCAAR(x), z) then result := MCADAR(x)
      else result := SUB2(MCDR(x), z)
    end;
  begin { MSUBLIS }
    if MATOM(x) then result := SUB2(x, y)
    else result := MCONS(MSUBLIS(x, MCAR(y)), MSUBLIS(x, MCDR(y)))
  end;

//-- e. functions as s-expressions -----------------------------

// In this section, McCarthy provides the rules for rewriting
// m-expressions as s-expressions.

// In pascal, our meta-language consitsts of the Sx()
// function, our various meta-functions, and the variables
// sTRUE and sNULL. We can even refer to our pascal functions
// as symbols by adding them to the 'metas' array and creating
// a new TExpr where kind=kMET.
//
// We will go ahead and create variables now for all of the routines
// of type (TExpr -> TExpr) that we've defined so far, as well as
// the ones we're about to define below.
var
  sAtomP, sEqP, sCar, sCdr, sCons, sFF, sSubst, sEqualP, sNullP,
  sCaar, sCadr, sCadar, sCaddr, sList, sAppend, sAmongP, sZip,
  sAssoc, sSublis : TExpr;

// and the new ones...
  sCond, sLambda, sLabel, sApply, sEval, sAppq,
  sMapList, sSearch, sFilter, sReduce,
  sAdd, sSub, sMul, sDiv, sMod, sLog, sDif : TExpr;

// ... for which we also have to provide forward declarations:
  function MCOND    ( x : TExpr ) : TExpr; forward;
  function MLAMBDA  ( x, y, z : TExpr ) : TExpr; forward;
  function MLABEL   ( x, y : TExpr ) : TExpr; forward;
  function MAPPLY   ( f, x : TExpr ) : TExpr; forward;
  function MEVAL    ( x : TExpr ) : TExpr; forward;
  function MAPPQ    ( f, x : TExpr ) : TExpr; forward;

  function MMAPLIST ( f, x : TExpr ) : TExpr; forward;
  function MSEARCH  ( f, x : TExpr ) : TExpr; forward;
  function MFILTER  ( f, x : TExpr ) : TExpr; forward;
  function MREDUCE  ( f, x, y : TExpr ) : TExpr; forward;

  function MADD ( x, y : TExpr ) : TExpr; forward;
  function MSUB ( x, y : TExpr ) : TExpr; forward;
  function MMUL ( x, y : TExpr ) : TExpr; forward;
  function MDIV ( x, y : TExpr ) : TExpr; forward;
  function MMOD ( x, y : TExpr ) : TExpr; forward;
  function MPOW ( x, y : TExpr ) : TExpr; forward;
  function MLOG ( x, y : TExpr ) : TExpr; forward;
  function MDIF ( x, y : TExpr ) : TExpr; forward;

// Finally, we will define one more TExpr variable, to hold
// the current environment (the list of variable bindings).
// It's format will be (((n0 . v1) (n1 . v1)...) ...)
// where the outermost list contains a stack of scopes,
// and each inner list contains name-value pairs. The
// CAR of mENV will be the innermost scope.
var mENV : TExpr;

function Define(n:string; x:TExpr) : TExpr;
  begin
    result := Sx(kSYM, Key(n)); // symbol representing the name
    // env: (((x . y) ...) ...) -> (((n . f) (x . y) ...) ...)
    mENV := MCONS(
      MCONS(MLIST(result, x),
            MCAAR(mENV)),
      MCDR(mENV));
  end;

procedure CreateBuiltins;
  begin
    sAtomP := Define('atom?', Meta(@MATOMP));
    sEqP := Define('eq?', Meta(@MEQP));
    sCar := Define('car', Meta(@MCAR));
    sCdr := Define('cdr', Meta(@MCDR));
    sCons := Define('cons', Meta(@MCONS));
    sFF := Define('ff', Meta(@MFF));
    sSubst := Define('subst', Meta(@MSUBST));
    sEqualP := Define('equal', Meta(@MEQUAL));
    sNullP := Define('null?', Meta(@MNULLP));
    sCaar := Define('caar', Meta(@MCAAR));
    sCadr := Define('cadr', Meta(@MCADR));
    sCadar := Define('cadar', Meta(@MCADAR));
    sCaddr := Define('caddr', Meta(@MCADDR));
    sList := Define('list', Meta(@MLIST));
    sAppend := Define('append', Meta(@MAPPEND));
    sAmongP := Define('among?', Meta(@MAMONGP));
    sZip := Define('zip', Meta(@MZIP));
    sAssoc := Define('assoc', Meta(@MASSOC));
    sSublis := Define('sublis', Meta(@MSUBLIS));
    sCond := Define('cond', Meta(@MCOND));
    sLambda := Define('lambda', Meta(@MLAMBDA));
    sLabel := Define('label', Meta(@MLABEL));
    sApply := Define('apply', Meta(@MAPPLY));
    sEval := Define('eval', Meta(@MEVAL));
    sAppq := Define('appq', Meta(@MAPPQ));
    sMapList := Define('maplist', Meta(@MMAPLIST));
    sSearch := Define('search', Meta(@MSEARCH));
    sFilter := Define('filter', Meta(@MFILTER));
    sReduce := Define('reduce', Meta(@MREDUCE));
    sAdd := Define('add', Meta(@MADD));
    sSub := Define('sub', Meta(@MSUB));
    sMul := Define('mul', Meta(@MMUL));
    sDiv := Define('div', Meta(@MDIV));
    sMod := Define('mod', Meta(@MMOD));
    sLog := Define('log', Meta(@MLOG));
    sDif := Define('dif', Meta(@MDIF));
  end;

// Now let's consider each of his translation rules, in order.
// Following McCarthy's lead, we'll use the notation E* to
// represents the s-expression translation of m-expression E.

// 1. for any s-expression E, E* is (quote E)
var sQUOTE : TExpr;
function Q(item:TExpr) : TExpr;
  begin
    result := MLIST(sQUOTE)
  end;

function MCOND( x : TExpr ) : TExpr;
  begin
  end;

function MLAMBDA( x, y, z : TExpr ) : TExpr;
  begin
  end;

function MLABEL( x, y : TExpr ) : TExpr;
  begin
  end;

//-- f. universal evaluator ------------------------------------

function MAPPLY( f, x : TExpr ) : TExpr;
  begin
  end;

function MEVAL( x : TExpr ) : TExpr;
  begin
  end;

function MAPPQ( f, x : TExpr ) : TExpr;
  begin
  end;

//-- g. higher order functions ---------------------------------

function MMAPLIST( f, x : TExpr ) : TExpr;
  begin
  end;

function MSEARCH( f, x : TExpr ) : TExpr;
  begin
  end;

function MFILTER( f, x : TExpr ) : TExpr;
  begin
  end;

function MREDUCE( f, x, y : TExpr ) : TExpr;
  begin
  end;


//-- arithmetic  -----------------------------------------------

function MADD( x, y : TExpr ) : TExpr;
  begin
  end;

function MSUB( x, y : TExpr ) : TExpr;
  begin
  end;

function MMUL( x, y : TExpr ) : TExpr;
  begin
  end;

function MDIV( x, y : TExpr ) : TExpr;
  begin
  end;

function MMOD( x, y : TExpr ) : TExpr;
  begin
  end;

function MPOW( x, y : TExpr ) : TExpr;
  begin
  end;

function MLOG( x, y : TExpr ) : TExpr;
  begin
  end;

function MDIF( x, y : TExpr ) : TExpr;
  begin
  end;


// - functions - - - - - - - - - - - - - - - - - - - - - - - - -
type
  TBind = record // name bindings.
            iden : integer; // index of a string
            cell : TCell;   // car=value cdr=attributes
          end;
  TDefTbl = specialize arrays.GArray<TBind>;

var
  ch   : char = #0;
  nest : string = '';

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
var
  line   : string;
  lx, ly : cardinal;
  done   : boolean = false;

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

procedure syntaxerror( const err: string );
  begin
    writeln( '=== syntax error at line ', ly, ', column ', lx, ': ===' );
    halt( err );
  end; { error }

function Depth : cardinal;
  begin
    result := Length(nest);
  end;

function NextChar( var ch : char ) : char;
  procedure prompt;
    begin
      { write the prompt first, because eof() blocks. }
      {$IFDEF NOPROMPT}
      {$NOTE compiling without prompt}
      {$ELSE}
      if length(nest) > 0
        then write( nest, prompt1 )
        else write( prompt0 );
      {$ENDIF}
      if eof then begin
        ch := ascii.EOT;
        line := ch;
        done := true;
        if depth > 0 then halt( 'unexpected end of file' );
        writeln;
        system.halt;
      end else begin
        readln( line );
        line := line + ascii.LF; { so we can do proper lookahead. }
        inc( ly );
        lx := 0;
      end
    end;
  begin
    while lx + 1 > length( line ) do prompt;
    inc( lx );
    ch := line[ lx ];
    // debug( '[ line ' + n2s( ly ) +
    //        ', column ' + n2s( lx ) + ' : ' +  ch + ']' );
    result := ch;
  end; { NextChar( ch ) }

// this recognizes decimal integers.
function IsNum( s : string; out num : integer ) : boolean;
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
  end;

function ReadAtom : TExpr;
  var tok : string = ''; i : integer;
  begin
    repeat tok := tok + ch until NextChar(ch) in stopchars;
    if IsNum( tok, i )
      then result := Sx( kINT, i )
      else result := Sx( kSYM, Key( tok ))
  end;

function PopChar( var s : string ) : char;
  var last : integer; ch : char;
  begin
    last := Length(s);
    if last = 0 then ch := #0 else ch := s[ last ];
    SetLength( s, last - 1 );
    result := ch;
  end;

function ReadString : TExpr;
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
  end;

procedure HandleDirective;
  var s : string;
  begin
    while ch <> ascii.LF do s += NextChar(ch);
    if AnsiStartsStr('fmt:struct', s) then showFormat := fmtStruct;
  end;

procedure SkipCommentsAndWhitespace;
  begin
    while ch in whitespace do
      if NextChar(ch) = commentChar then
        if NextChar(ch) = '%' then HandleDirective
        else while ch <> ascii.LF do NextChar(ch);
  end;

function ReadListEnd : TExpr;
  var expect : char;
  begin
    if Length(nest) = 0 then
      result := Sx(kERR, Key('Unexpected char: ' + ch))
    else begin
      case PopChar(nest) of
        '{' : expect := '}';
        '[' : expect := ']';
        '(' : expect := ')';
        else expect := '?' // should never happen
      end;
      if ch = expect then result := sNULL
      else result := Sx(kERR, Key('List end mismatch. Expected: '
                         + expect + ', got: ' + ch));
    end;
    NextChar(ch);
  end; { ReadListEnd }

function ShowExpr(expr :TExpr) : string; Forward;
function ReadNext( out value : TExpr ): TExpr;

  function ReadList( out res : TExpr; AtHead : boolean) : TExpr;
    var car, cdr : TExpr;
    begin
      if AtHead then begin nest += ch; NextChar(ch) end;
      SkipCommentsAndWhitespace;
      if (ch in [')', ']', '}']) then
        begin
          res := sNULL; NextChar(ch);
        end
      else if ReadNext(car).kind = kERR then res := car
      else if ReadList(cdr, false).kind = kERR then res := cdr
      else res := MCons(car, cdr);
      if AtHead then PopChar(nest);
      result := res;
      // debug('List -> ' + k2s(res.kind) + ' : ' + ShowExpr(res));
    end; { ReadList }

  function ReadQuote : TExpr;
    begin
      NextChar(ch);
      if ReadNext(result).kind <> kERR
        then result := MCons(Sx(kSym, Key('quote')), result)
    end; { ReadQuote }

  begin
    SkipCommentsAndWhitespace;
    case ch of
      '(','[','{' : ReadList(result, true);
      ')',']','}' : result := ReadListEnd;
      '"'         : result := ReadString;
      ''''        : result := ReadQuote;
      else result := ReadAtom;
    end;
    value := result;
  end; { ReadNext }

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
    result := Sx(kERR, Key('Eval Error'));
    if itm.kind = kCEL then with cells[ itm.data ] do
      begin
        if car.kind = kSTR then
          if syms[car.data] = 'quote' then
            result := FQuote(cdr)
      end
    else result := itm;
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

var val : TExpr;
begin
  syms := TSymTbl.Create;
  cells := TCellTbl.Create;
  defs := TDefTbl.Create;
  CreateBooleans;
  CreateBuiltins;
  repeat Print(Eval(ReadNext(val)))
  until (val.kind = kERR)
end.
