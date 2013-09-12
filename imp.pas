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
//
// The model presented here is largely based on John McCarthy's
// LISP system, described in his 1960 paper, "Recursive Functions
// of Symbolic Expressions and Their Computation by Machine, Part I"
// http://www-formal.stanford.edu/jmc/recursive/
//
// Specifically, we're translating this page:
//
//    http://www-formal.stanford.edu/jmc/recursive/node3.html
//
//-- a. symbolic expressions -----------------------------------
//
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
    kMET); // a meta-function (TExpr->TExpr, implemented in pascal)
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
const atomic = [kSYM..kMET] - [kCEL];

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
// m-expressions to pascal functions.
type
  TMetaFun = function (var expr : TExpr) : TExpr;

// An s-expression of kind=kMET is therefore not an M-expression
// but a symbol that represents a particular pascal function of
// this type.
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
  TMetaTbl = array [0..31] of TMetaFun;
var
  metas	    : TMetaTbl;
  metacount : cardinal = 0;

// Meta adds a function record to the 'metas' table and constructs
// a unique symbol for it.
function Meta( f : TMetaFun ) : TExpr;
  begin
    metas[metacount] := f;
    if metacount > high(metas) then halt( 'out of meta slots.' );
    result := Sx(kMET, metacount);
    inc(metacount);
  end;

//-- c. elementary meta-expressions ----------------------------

// These are the elementary expressions from the 1960 LISP paper.
//
// The M prefix used in these routines is short for 'meta', since
// we're using pascal as a meta-language to describe lisp. As a
// convention, I will also type meta function names in ALL CAPS.

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

//-- d. recursive meta-expressions -----------------------------

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
var { common symbols }
  NullSym : TExpr;
  TrueSym : TExpr;
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
      kMET : result := 'MET';
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
      if ch = expect then result := NullSym
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
          res := NullSym; NextChar(ch);
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
      kMET : result := '<' + IntToStr( expr.data ) + '>';
    end;
    if showFormat = fmtStruct then
      case expr.kind of
        KNUL,
        kERR,
        kSYM,
        kSTR : result := 's:' + result;
        kINT : result := 'n:' + result;
        kMET : result := 'm:' + result;
        kCEL : result := ShowList( expr, true );
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
  NullSym := Sx(kNUL, Key('()'));
  TrueSym := Sx(kSYM, Key('T'));
  repeat Print(Eval(ReadNext(val)))
  until (val.kind = kERR)
end.
