// -------------------------------------------------------------
// implish: an imperative meta-programming language.
//
// Copyright 2013 Michal J Wallace <http://tangentstorm.com/>
// Avaliable to the public for use under the MIT/X11 License.
// -------------------------------------------------------------
{$mode objfpc}{$i xpc.inc}
program imp(input, output);
uses xpc, arrays, stacks, ascii, sysutils, strutils, num;

type
  TKind = (kNUL, kERR, kINT, kSYM, kSTR, kCEL, kFUN);
  TExpr = record
            kind : TKind;
            data : integer;
          end;
  TCell = record
            car, cdr : TExpr
          end;
  TBind = record // name bindings.
            iden : integer; // index of a string
            cell : TCell;   // car=value cdr=attributes
          end;
  TSymTbl = specialize GEqArray<string>;
  TDefTbl = specialize GArray<TBind>;
  TCelTbl = specialize GArray<TCell>;
  TPasFun = function (var expr : TExpr) : TExpr;
  TFunTbl = array [0..31] of TPasFun;

var
  ch   : char = #0;
  nest : string = '';
  syms : TSymTbl;
  cels : TCelTbl;
  defs : TDefTbl;
  funs : TFunTbl; funct : cardinal = 0;
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
      kFUN : result := 'FUN';
    end
  end;

procedure debug( msg : string ); inline;
  begin
    if debugging then writeln( msg )
  end;

//-- read part -------------------------------------------------

procedure error( const err: string );
  begin
    write( 'error at line ', ly, ', column ', lx, ': ' );
    writeln( err );
    halt;
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
        if depth > 0 then error( 'unexpected end of file' );
        writeln;
        halt; { todo : remove this once depth-checking works correctly }
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

function Sx( kind : TKind; data : integer ) : TExpr;
  begin
    result.kind := kind;
    result.data := data;
  end;

function Fun( f : TPasFun ) : TExpr;
  begin
    funs[funct] := f;
    inc(funct);
    if funct > high(funs) then error( 'out of function slots.' );
  end;

function Sym( s : string ) : cardinal;
  begin
    if not syms.Find( s, result ) then result := syms.Append( s );
  end;

function Cons( head, tail : TExpr ) : TExpr;
  var cell : TCell;
  begin
    cell.car := head;
    cell.cdr := tail;
    result := Sx( kCEL, cels.Append( cell ));
  end;

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
      else result := Sx( kSYM, Sym( tok ))
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
    result := Sx(kSTR, Sym(s))
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
      result := Sx(kERR, Sym('Unexpected char: ' + ch))
    else begin
      case PopChar(nest) of
        '{' : expect := '}';
        '[' : expect := ']';
        '(' : expect := ')';
        else expect := '?' // should never happen
      end;
      if ch = expect then result := NullSym
      else result := Sx(kERR, Sym('List end mismatch. Expected: '
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
      else res := Cons(car, cdr);
      if AtHead then PopChar(nest);
      result := res;
      // debug('List -> ' + k2s(res.kind) + ' : ' + ShowExpr(res));
    end; { ReadList }

  function ReadQuote : TExpr;
    begin
      NextChar(ch);
      if ReadNext(result).kind <> kERR
        then result := Cons(Sx(kSym, Sym('quote')), result)
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

//-- eval part -------------------------------------------------
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
    result := Sx(kERR, Sym('Eval Error'));
    if itm.kind = kCEL then with cels[ itm.data ] do
      begin
        if car.kind = kSTR then
          if syms[car.data] = 'quote' then
            result := FQuote(cdr)
      end
    else result := itm;
  end;

//-- print part ------------------------------------------------

function DumpCell( ref : TExpr ): string;
  var cell : TCell;
  begin
    cell := cels[ ref.data ];
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
      cell := cels[ ref.data ];
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
      kFUN : result := '<' + IntToStr( expr.data ) + '>';
    end;
    if showFormat = fmtStruct then
      case expr.kind of
        KNUL,
        kERR,
        kSYM,
        kSTR : result := 's:' + result;
        kINT : result := 'n:' + result;
        kFUN : result := 'f:' + result;
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
  cels := TCelTbl.Create;
  defs := TDefTbl.Create;
  NullSym := Sx(kNUL, Sym('()'));
  TrueSym := Sx(kSYM, Sym('T'));
  Def(Sym('quote'), Fun(@FQuote));
  repeat Print(Eval(ReadNext(val)))
  until (val.kind = kERR)
end.
