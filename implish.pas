{$mode objfpc}{$H+}
unit implish;
interface uses variants, classes, sysutils;
{ ------------------------------------------------------------ }

type
  TImp = class (TObject)
    procedure Send( s : string );
    function Eval : variant;
    function Ready : boolean;
    function Terminated : boolean;
  end;

procedure repl;

{ ------------------------------------------------------------ }
implementation

procedure TImp.Send( s : string );
  begin
  end;

function TImp.Eval : variant;
  begin
    result := null
  end;

function TImp.Ready : boolean;
  begin
    result := true
  end;

function TImp.Terminated : boolean;
  begin
    result := true
  end;

procedure repl;
  var imp : TImp; s : string;
  begin
    imp := TImp.Create;
    repeat
      ReadLn(s);
      imp.Send(s);
      if imp.Ready then WriteLn(VarToStr(Imp.Eval));
    until imp.Terminated;
    imp.Destroy;
  end;
  
begin
end.
