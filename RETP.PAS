program RETROP;
uses crt, objects, drivers, views;

{-- misc -------------------------}
const
  on = true;
  off = false;
type
  set32 = set of 0..31;


{-- screen IO --------------------}
const
  kScrW = 80;
  kScrH = 25;
type
  ScreenBuff = ^ScreenData;
  ScreenData = array[ 0 .. (2 * kScrH * kScrW)-1 ] of byte;
var
  screen: ScreenData absolute $B800:$0000;
  view  : TView;  { to get cursor support and string drawing }
  drawto: ScreenBuff;
  buffln: TDrawBuffer;  { a single line of char+attr words }

procedure colorXY( c, x, y : byte; s : string);
  var i : byte; offs : word;
  begin
    offs := 2 * (y * kScrw + x);
    FillChar(drawto^[offs], length(s)*2, c);
    for i := 1 to length(s) do
      begin
        drawto^[offs] := byte(s[i]);
        inc(offs,2)
      end
  end;

{ use 16 background colors instead of blinking text }
procedure blinking( b : boolean );
 begin
   asm
     mov ah,$10;
     mov al,$03;
     mov bl,b;
     int 10h;
   end
 end;

{-- dynamic types -----------------}
type
   Obj = ^BaseObj; { base type for all objects }
  Atom = ^AtomObj; { atomic values }
   Int = ^IntObj;  { holds a 32-bit integer }
   Str = ^StrObj;  { a pascal string }
                   { TODO : Txt = ^TxtObj; }
  Cell = ^CellObj;
   Ref = ^RefObj;

  BaseObj = object(objects.TObject)
    function Str: string; virtual;
    destructor Destroy; virtual;
  end;

  AtomObj = object(BaseObj)
  end;

  IntObj = object(AtomObj)
    value : longint;
    function Str: string; virtual; { override }
  end;

  StrObj = object(AtomObj)
    value : string;
    function Str: string; virtual; { override }
  end;

  CellObj = object(BaseObj)
    head, tail : Obj;
    constructor Create( headObj, tailObj : Obj );
    function Str: string; virtual; { override }
  end;

  RefObj = object(AtomObj)
    head, tail : Obj;
  end;

var
  null : Atom;
  root : Ref;

function BaseObj.Str : string;
  begin
    Str := '$';
  end;

destructor BaseObj.Destroy;
  begin
  end;

function IntObj.Str : string;
  var result : string[11];
  begin
    system.Str(value, result);
    Str := result
  end;

function StrObj.Str : string;
  begin
    Str := value;
  end;

constructor CellObj.Create( headObj, tailObj : Obj );
  begin
    head := headObj;
    tail := tailObj;
    if head = nil then head := null;
    if tail = nil then tail := null;
  end;

function CellObj.Str : string;
  var result : string;
  begin
    result := '(' + head^.Str;
    if pointer(tail) = pointer(null) then
      result := result + ' ' + tail^.Str;
    Str := result  + ')';
  end;

{-- fixed-size data blocks --------}
type
  Block = array[ 0 .. 1023 ] of byte;
  Drive = file of block;

{-- variable-sized buffers --------}
type
  Bytes  = array[ 0..0 ] of byte;
  Buffer = ^Bytes;

{-- display -----------------------}
type

  Point = object
    x, y : integer;
  end;

  Quad = object( Point )
    w, h : integer;
    function x2 : integer;
    function y2 : integer;
  end;

function Quad.x2 : integer;
  begin
    x2 := x + w
  end;

function Quad.y2 : integer;
  begin
    y2 := y + h
  end;

{-- tagged data types -------------}
type
  Tagged  = ^TaggedObj;
  Symbol  = ^TokenObj;    { for symbol/lookup tables }
  Token   = ^TokenObj;    { for parsing long texts }

  TaggedObj = object(BaseObj)
    tag : longint;
  end;

  SymbolObj = object(TaggedObj)
    name : string[32];
  end;

  TokenObj = object(TaggedObj)
    sym : Symbol;
    line, column, span : longint;
  end;

{-- Tuples ---------------------------}
type
  TypeDef  = ^TypeDefObj;
  FieldDef = ^FieldDefObj;
  Tuple    = ^TupleObj;    { generic record/struct }
  Message  = ^MessageObj;  { for message passing }

  TypeKind = ( tkSimple, tkTkUnion, tkFunction, tkSchema );

  TypeDefObj  = object(BaseObj)
    size : Word;
    kind : TypeKind;
    numFields : byte;
    first : FieldDef;
  end;

  FieldDefObj = object(BaseObj)
    next : FieldDef;
    name : Symbol;
  end;

  TupleObj = object(TokenObj)
    meta : TypeDef;
    data : Buffer;
  end;

  MessageObj = object(TaggedObj)
    sym : Symbol;
    args: Tuple;
  end;


{-- actors ------------------------}
const
  cmd_quit  =  -1;
  cmd_step  =  -2;
  cmd_draw  =  -3;
  cmd_hide  =  -4;
  cmd_show  =  -5;
  cmd_help  =  -6;
  evt_keydn = -25;
  evt_keyup = -26;
  evt_mosdn = -27;
  evt_mosup = -28;
  evt_mosmv = -29;

type
  Actor = ^ActorObj;
  Group = ^GroupObj;
  Morph = ^MorphObj;

  ActorObj = object
    active,           { wants update() }
    alive,            { exists but not alive triggers gc }
    visible,          { to allow hide/show }
    exists : boolean; { turn off everything at once }
    constructor Create;
    destructor  Destroy; virtual;
    procedure Update; virtual;
    procedure Render; virtual;
    function Handle( msg : Token ):boolean; virtual;
  end;

  GroupObj = object( ActorObj )
  end;

  MorphObj = object( GroupObj )
    bounds : Quad;
    colors : word; { foreground and background }
    constructor Create;
    procedure Draw; virtual;
  end;

constructor ActorObj.Create;
  begin
    alive  := true;
    active := true;
    exists := true;
    visible := false;
  end;

destructor ActorObj.Destroy;
  begin
  end;

procedure ActorObj.Render;
  begin
  end;

procedure ActorObj.Update;
  begin
  end;

function ActorObj.Handle( msg : Token ):boolean;
  begin
    case msg^.tag of
      cmd_quit:
        begin
          active := false;
          Handle := true;
        end;
      cmd_draw:
        Render;
      cmd_step:
        Update;
      else
        Handle := false { didn't handle, so let the next guy try }
    end
  end;

constructor MorphObj.Create;
  begin
    ActorObj.Create;
    visible := true;
  end;

procedure MorphObj.Draw;
  begin
    WriteLn('morph')
  end;

{-- stack -------------------}
type
  Stack    = ^StackObj;
  StackObj = object
    slots : array[ 0..254 ] of longint;
    count : byte;
    procedure Push( val : longint );
    function  Pop : longint;
    function  tos : longint;
    function  nos : longint;
    procedure Swap;
    procedure Dup;
    procedure Over;
    procedure Rot;
  end;

procedure StackObj.Push( val : longint );
  begin
    slots[count] := val;
    inc(count)
  end;

function StackObj.Pop : longint;
  begin
    Dec(count);
    Pop := slots[count];
  end;

function StackObj.tos : longint;
  begin
    tos := slots[count-1]
  end;

function StackObj.nos : longint;
  begin
    nos := slots[count-2]
  end;

procedure StackObj.Swap;
  var tmp : longint;
  begin
    tmp := tos;
    slots[ count-1 ] := nos;
    slots[ count-2 ] := tmp;
  end;

procedure StackObj.Dup;
  begin
    Push(tos)
  end;

procedure StackObj.Over;
  begin
    Push(tos)
  end;

procedure StackObj.Rot;
  var tmp : longint;
  begin
    tmp := slots[count-3];
    slots[count-3] := slots[count-2];
    slots[count-2] := slots[count-1];
    slots[count-1] := tmp;
  end;

{-- virtual machine ------------}
type
  OpCode = (opNop, opNot, opXor, opAnd,
            opDup, opDrp, opPsh, opPop,
            opSwp, opRot,
            opFrk, opSpn, opSnd, opYld,
            opAdd, opSub, opMul, opDvm,
            opInc, opDec, opShr, opShl,
            opCmp, opGT,  opLT,  opEq, opIn,
            opJmp, opEls, opRet, opZex,
            opNxt, opGet, opPut );
type
  Machine  = ^MachineObj;
  MachineObj = object( MorphObj )
    ibuf, obuf : string; { input/output buffers (255 chars) }
    ip, rp, wp : byte;
    data, addr : stack;
    memory     : buffer;
    procedure Update; virtual; { override; }
    procedure Render; virtual; { override; }
    procedure RunOp( op:OpCode );
  end;

procedure MachineObj.RunOp( op:OpCode );
  var temp : longint;
  begin
    with data^ do case op of
      opNop : begin end;
      opNot : push(not pop);
      opXor : push(pop xor pop);
      opAnd : push(pop and pop);
      opDup : dup;
      opDrp : temp := pop;
      opPsh : addr^.push(pop);
      opPop : push(addr^.pop);
      opSwp : swap;
      opRot : rot;
      opFrk : begin {-- todo: fork --} end;
      opSpn : begin {-- todo: spawn --} end;
      opAdd : push(pop + pop);
      opSub : push(pop - pop);
      opMul : push(pop * pop);
      opDvm :
        begin
          addr^.push( tos mod nos );
          push( pop div pop );
          push( addr^.pop );
        end;
      opInc : push(succ(pop));
      opDec : push(pred(pop));
      opShl : push(pop shl pop);
      opShr : push(pop shr pop);
      opCmp : begin
                temp := pop - pop;
                if temp > 0 then push(1)
                else if temp < 0 then push(-1)
                else push(0)
              end;
      opGt : if pop > pop then push(-1) else push(0);
      opLt : if pop < pop then push(-1) else push(0);
      opEq : if pop = pop then push(-1) else push(0);
      opIn : begin end;{--todo-- if (pop mod 32) in set32(pop)
                         then push(-1) else push(0); }
      opJmp: ip := pop;
      opEls: if pop = 0 then begin {---todo-- ip:= memory^(ip) --} end
                        else inc(ip);
      opRet: ip := addr^.pop;
      opZex: if tos = 0 then begin temp := pop; ip := addr^.pop end;
      opNxt: if addr^.tos = 0
               then begin temp:=pop; temp := addr^.pop end
               else begin addr^.over; ip := pop end;
      opGet: push(memory^[pop]);
      opPut: memory^[pop] := pop;
      opSnd: begin end; {-- todo --}
      opYld: begin end; {-- todo --}
    end
  end;

procedure MachineObj.Update;
  begin
  end;

procedure MachineObj.Render;
  var i,j : integer;
  begin
    for i := 1 to 64 do
      for j := 1 to 16 do
        colorxy( random(8), i, j, 'x' );
  end;

{-- concurrency --------------------}

var actors : array[ 0 .. 254 ] of Actor;
    tokens : array[ 0 .. 254 ] of Token;
    numActors : byte;
    numTokens : byte;

procedure Register(this:Actor);
  begin
    if numActors < 255 then
      begin
        actors[numActors] := this;
        inc(numActors);
      end
    else
      begin
        Dispose(this, Destroy);
        Writeln('out of actor slots');
      end
  end;

procedure Create;
  begin
    InitEvents; HideMouse;
    numActors := 0; numTokens := 0;
    Register(New(Machine, Create));
    InitVideo; ClearScreen;
    drawto := @screen;
    ShowMouse;
  end;

procedure Update;
  var i : byte; e : TEvent; a : Actor;
  begin
    GetKeyEvent(e);
    if (e.what = evKeyDown) then
      case e.KeyCode of
        kbEsc  : halt;
      else
        case chr(e.KeyCode) of
          '0'  : blinking(on);
          '1'  : blinking(off);
        else
          write(chr(e.KeyCode))
        end
      end;

    { dispatch to all actors }
    i := 0;
    while i < numActors do
      begin
        a := actors[ i ];
        if a^.active then
          begin
            a^.Update;
            if a^.alive then
              inc(i)
            else
              begin
                Dec(numActors);
                Dispose(a, Destroy);
                actors[ i ] := Actors[ numActors ];
                actors[ numActors ] := nil;
              end
          end
        else inc(i) { was inactive, skip over for now }
      end
  end;

procedure Render;
  var i : byte;
  begin
    if numActors > 0 then
      for i := 0 to numActors-1 do
        if actors[ i ]^.Visible then actors[ i ]^.Render
  end;

procedure Destroy;
  begin
    HideMouse;
    DoneEvents;
    DoneVideo;
  end;

var rect : TRect;
begin
  Create;
  begin
    HideMouse;
    rect.Assign(1,1,20,20);
    view.Init(rect); blinking(off);
    colorxy( $e0, 0, 0, 'hello world');
    colorxy( $60, 1, 1, 'hello world');
    colorxy( $0E, 22, 10, #2);
    ShowMouse;
  end;
  repeat
    Update;
    Render;
  until numActors = 0;
  Destroy;
end.