// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

/// Viel geändert von Jens Biermann am 07.02.2012
/// Viel geändert von Jens Biermann am 29.01.2015
/// Änderungen von Jens Biermann am 23.08.2016
/// Items in TVariables - Jens Biermann am 10.09.2016

unit NewMathParser.Oper;

interface

uses System.Classes, System.Generics.Collections, System.SysUtils;

const
  cNoError = 0;
  // Internal error:
  cInternalError = 1;
  // Expression errors:
  cErrorInvalidChar   = 2;
  cErrorUnknownName  = 3;
  cErrorInvalidFloat = 4;
  cErrorOperator     = 5;
  cErrorInvalidOperator  = 16;
  // cErrorFxNeedLeftBracket     = 6; deprecated
  cErrorNotEnoughArgs         = 7;
  cErrorSeparatorNeedArgument = 8;
  cErrorMissingLeftBrackets   = 9;
  cErrorMissingRightBrackets  = 10;
  cErrorLeftBracket           = 11;
  cErrorRightBracket          = 12;
  cErrorSeparator             = 13;
  cErrorOperatorNeedArgument  = 14;
  cErrorToManyArgs            = 15;
  cErrorAssignmentError       = 17;
  // Calc errors:
  cErrorCalc           = 100;
  cErrorDivByZero      = 101;
  cErrorPower          = 102;
  cErrorFxInvalidValue = 103;
  cErrorTan            = 104;

const
  Numbers = ['0' .. '9'];
  Letters = ['a' .. 'z'];

type

  EParseError = class(Exception);

  PError = ^TError;

  TError = record
  private
    FCode    : Integer;
    FPosition: Integer;
    FName    : string;
  public
    constructor Create(ACode, APosition: Integer; AName: string);
    procedure Clear;
    function ToString: string;
    function IsNoError: Boolean;
    property Code: Integer read FCode write FCode;
    property Position: Integer read FPosition write FPosition;
    property Name: string read FName write FName;
  end;

  TArgStack = TArray<TFunc<Double>>;

  TOpFunc    = reference to function(Values: TArgStack): Double;
  TErrorFunc = reference to function(Values: TArgStack): Integer;

  TOpFunc_Legacy    = reference to function(Values: TArray<Double>): Double;
  TErrorFunc_Legacy = reference to function(Values: TArray<Double>): Integer;

  TOperator = class(TObject)
  private
    FErrorFunc: TErrorFunc;
    FPriority : Double;
    FArguments: Integer;
    FName     : string;
    FFunc     : TOpFunc;
  public
    constructor Create(aPriority: Double; aArguments: Integer; aName: string); overload;
    constructor Create(aPriority: Double; aArguments: Integer; aName: string; aOpF: TOpFunc); overload;
    constructor Create(aPriority: Double; aArguments: Integer; aName: string; aOpF: TOpFunc; aIsError: TErrorFunc); overload;
    constructor Create(aPriority: Double; aArguments: Integer; aName: string; aOpF: TOpFunc_Legacy); overload;
    constructor Create(aPriority: Double; aArguments: Integer; aName: string; aOpF: TOpFunc_Legacy; aIsError: TErrorFunc_Legacy); overload;
    function Error(Values: TArgStack): Integer;
    property Name: string read FName write FName;
    property Func: TOpFunc read FFunc write FFunc;
    property Priority: Double read FPriority write FPriority;
    property Arguments: Integer read FArguments write FArguments;
  end;

  TOperation = class(TObjectList<TOperator>)
  private type
    TCharSet = set of ansichar;
  private
    FOpChars: TCharSet;
    procedure AddOpNone;
    procedure AddOpNeg;
    procedure AddOpBrackets;
    function ValidVariableName(Name: string): Boolean;
    function GetOp(aName: string): TOperator;
    procedure HandleAddedItems(Sender: TObject; const Item: TOperator;
      Action: TCollectionNotification);
  public
    constructor Create;
    // destructor Destroy; override;
    function AddCustomOperation(Name: string; Arguments: Integer; Priority: byte): Boolean;
    function IndexOfName(aName: string): Integer;
    function Contains(Name: string): Boolean;
    function RenameOperation(CurrentName, NewName: string): Boolean;
    property Op[aName: string]: TOperator read GetOp; default;
    property OpChars: TCharSet read FOpChars write FOpChars;
  end;

procedure AddOperation(AOperation: TOperation);
procedure AddMath(AOperation: TOperation);
procedure AddTrigonometry(AOperation: TOperation);
procedure AddTrigonometryDeg(AOperation: TOperation);
procedure AddLogarithm(AOperation: TOperation);
procedure AddComparisons(AOperation: TOperation);
procedure AddLogic(AOperation: TOperation);
procedure AddAssignment(AOperation: TOperation);

type

  TTypeStack = (tsValue, tsOperator, tsFunction, tsLeftBracket, tsRightBracket, tsSeparator, tsVariable);

  TParserValueFunc = function(ArgStack: TFunc<Double>): double;

  TParserItem = class
  strict private
    FValue         : Double;
    FValueFunc     : TFunc<Double>;
    FTypeStack     : TTypeStack;
    FName          : string;
    FArgumentsCount: Integer;
    FTextPos       : Integer;
    function GetIsFunc: Boolean;
  private
    function GetValue: Double;
    function GetValueFunc: TFunc<Double>;
  public
    constructor Create(aTypeStack: TTypeStack; APos: Integer; aName: string); overload;
    constructor Create(aValue: Double; APos: Integer; aName: string); overload;
    constructor Create(aValue: TFunc<Double>; APos: Integer; aName: string); overload;
    constructor Create(aItem: TParserItem); overload;
    procedure Assign(Source: TObject);
    procedure Write(S: TStream);
    procedure Read(S: TStream);
    property Name: string read FName write FName;
    property ArgumentsCount: Integer read FArgumentsCount write FArgumentsCount;
    property Value: Double read GetValue write FValue;
    property ValueFunc: TFunc<Double> read GetValueFunc write FValueFunc;
    property TypeStack: TTypeStack read FTypeStack write FTypeStack;
    property TextPos: Integer read FTextPos write FTextPos;
  end;

procedure ClearAndFreeStack(S: TStack<TParserItem>);

implementation

uses
  System.Math;

{ TOperator }

constructor TOperator.Create(aPriority: Double; aArguments: Integer; aName: string);
begin
  inherited Create;
  FPriority  := aPriority;
  FArguments := aArguments;
  FName      := aName;
end;

constructor TOperator.Create(aPriority: Double; aArguments: Integer; aName: string; aOpF: TOpFunc);
begin
  Create(aPriority, aArguments, aName);
  FFunc      := aOpF;
  FErrorFunc := nil;
end;

constructor TOperator.Create(aPriority: Double; aArguments: Integer; aName: string; aOpF: TOpFunc; aIsError: TErrorFunc);
begin
  Create(aPriority, aArguments, aName, aOpF);
  FErrorFunc := aIsError;
end;

constructor TOperator.Create(aPriority: Double; aArguments: Integer; aName: string; aOpF: TOpFunc_Legacy);
begin
  Create(aPriority, aArguments, aName);
  FFunc      := function (ArgStack: TArgStack): Double
  var
    i: integer;
    Values: TArray<Double>;
  begin
    SetLength(Values, Length(ArgStack));

    for i := 0 to Length(ArgStack) - 1 do
      Values[i] := ArgStack[i]();

    Result := aOpF(Values);
  end;
  FErrorFunc := nil;
end;

constructor TOperator.Create(aPriority: Double; aArguments: Integer; aName: string; aOpF: TOpFunc_Legacy; aIsError: TErrorFunc_Legacy);
begin
  Create(aPriority, aArguments, aName, aOpF);
  FErrorFunc := function (ArgStack: TArgStack): Integer
  var
    i: integer;
    Values: TArray<Double>;
  begin
    SetLength(Values, Length(ArgStack));

    for i := 0 to Length(ArgStack) - 1 do
      Values[i] := ArgStack[i]();

    Result := aIsError(Values);
  end;
end;

function TOperator.Error(Values: TArgStack): Integer;
begin
  if Assigned(FErrorFunc) then
    Result := FErrorFunc(Values)
  else
    Result := cNoError;
end;

{ TOperationen }

constructor TOperation.Create;
begin
  inherited Create(True);

  OnNotify := HandleAddedItems;

  AddOpNone;
  AddOpNeg;
  AddOpBrackets;
end;

function TOperation.Contains(Name: string): Boolean;
begin
  Result := IndexOfName(Name) <> -1;
end;

function TOperation.IndexOfName(aName: string): Integer;
var
  i: Integer;
begin
  for i := 0 to Count - 1 do
    if SameText(Self.Items[i].FName, aName) then
      Exit(i);
  Result := -1;
end;

function TOperation.GetOp(aName: string): TOperator;
var
  iP: TOperator;
begin
  for iP in Self do
    if SameText(iP.FName, aName) then
      Exit(iP);

  Result := nil;
end;

procedure TOperation.HandleAddedItems(Sender: TObject; const Item: TOperator;
  Action: TCollectionNotification);
var
  c: Char;
begin
  if Action = cnAdded then begin
    for c in Item.Name do
      if not CharInSet(c, Numbers + Letters) then

      Include(FOpChars, AnsiChar(c));
  end;
end;

function TOperation.RenameOperation(CurrentName, NewName: string): Boolean;
var
  i: Integer;
begin
  Result := False;
  if NewName = '' then
    Exit;
  NewName := AnsiLowerCase(NewName);
  if not ValidVariableName(NewName) then
    Exit;

  i := IndexOfName(AnsiLowerCase(CurrentName));

  if i <> -1 then
  begin
    Self.Items[i].FName := NewName;
    Result              := True;
  end;
end;

function TOperation.ValidVariableName(Name: string): Boolean;
/// Determine if variable Name is defined with 'a'..'z', '_'
/// and does not enter in conflict with function Names:
var
  i: Integer;
begin
  Result := False;
  Name   := trim(AnsiLowerCase(Name));
  if (Name = '') or (Name = 'e') then
    Exit; // ex: 5E3 = 5 * 10*10*10
  if IndexOfName(Name) <> -1 then
    Exit;
  if not CharInSet(Name[1], ['_'] + Letters) then
    Exit;

  for i := 2 to Length(Name) do
    if not CharInSet(Name[i], ['_'] + Letters + Numbers) then
      Exit(True);
end;

procedure TOperation.AddOpNone;
begin
  Add(TOperator.Create(0, 0, ''));
end;

procedure TOperation.AddOpNeg;
begin
  // Internal functions
  // OpNeg (negative value, used for diferenciate with substract operator)
  Add(TOperator.Create(4, 1, 'neg',
    function(Values: TArray<Double>): Double
    begin
      Result := -Values[0];
    end));
end;

procedure TOperation.AddOpBrackets;
begin
  // Internal functions
  // OpBrackets, for holding multiple statements in brackets
  Add(TOperator.Create(0, -1, 'substatement',
    function(ArgStack: TArgStack): Double
    var
      i: Integer;
    begin
      Result := 0;
      for i := 0 to Length(ArgStack)-1 do
        Result := ArgStack[i]();
    end));
end;

function TOperation.AddCustomOperation(Name: string; Arguments: Integer; Priority: byte): Boolean;
begin
  Name := AnsiLowerCase(Name);
  if ValidVariableName(Name) then
  begin
    Add(TOperator.Create(Priority, Arguments, Name));
    Exit(True);
  end;
  Result := False;
end;

procedure AddOperation(AOperation: TOperation);
begin
  // Add
  AOperation.Add(TOperator.Create(1, 2, '+',
    function(Values: TArray<Double>): Double
    begin
      Result := Values[0] + Values[1];
    end));

  // subtract
  AOperation.Add(TOperator.Create(1, 2, '-',
    function(Values: TArray<Double>): Double
    begin
      Result := Values[0] - Values[1];
    end));

  // Multi
  AOperation.Add(TOperator.Create(2, 2, '*',
    function(Values: TArray<Double>): Double
    begin
      Result := Values[0] * Values[1];
    end));

  // Divide
  AOperation.Add(TOperator.Create(2, 2, '/',
    function(Values: TArray<Double>): Double
    begin
      Result := Values[0] / Values[1];
    end,
    function(Values: TArray<Double>): Integer
    begin
      if Values[1] = 0 then
        Result := cErrorDivByZero
      else
        Result := cNoError;
    end));

  // Power
  AOperation.Add(TOperator.Create(3, 2, '^',
    function(Values: TArray<Double>): Double
    begin
      Result := Power(Values[0], Values[1]);
    end,
    function(Values: TArray<Double>): Integer
    begin
      if (frac(Values[1]) <> 0) and (Values[0] < 0) then
        Result := cErrorPower
      else
        Result := cNoError;
    end));

  // Mod
  AOperation.Add(TOperator.Create(2, 2, '%',
    function(Values: TArray<Double>): Double
    var
      x, y: Double;
    begin
      x := Values[0];
      y := Values[1];
      Result := x - int(x / y) * y;
    end,
    function(Values: TArray<Double>): Integer
    begin
      if Values[1] = 0 then
        Result := cErrorDivByZero
      else
        Result := cNoError;
    end));
end;

procedure AddMath(AOperation: TOperation);
begin
  // Absolute
  AOperation.Add(TOperator.Create(0, 1, 'abs',
    function(Values: TArray<Double>): Double
    begin
      Result := Abs(Values[0]);
    end,
    function(Values: TArray<Double>): Integer
    begin
      if (Length(Values) > 1) then
        Result := cErrorToManyArgs
      else
        Result := cNoError;
    end));

  // Max
  AOperation.Add(TOperator.Create(0, -1, 'max',
    function(Values: TArray<Double>): Double
    begin
      Result := MaxValue(Values);
    end,
    function(Values: TArray<Double>): Integer
    begin
      if (Length(Values) < 2) then
        Result := cErrorNotEnoughArgs
      else
        Result := cNoError;
    end));

  // Min
  AOperation.Add(TOperator.Create(0, -1, 'min',
    function(Values: TArray<Double>): Double
    begin
      Result := MinValue(Values);
    end,
    function(Values: TArray<Double>): Integer
    begin
      if (Length(Values) < 2) then
        Result := cErrorNotEnoughArgs
      else
        Result := cNoError;
    end));

  // RoundTo
  AOperation.Add(TOperator.Create(0, 2, 'roundto',
    function(Values: TArray<Double>): Double
    begin
      Result := RoundTo(Values[0], round(Values[1]));
    end));

  // Sqrt
  AOperation.Add(TOperator.Create(0, 1, 'sqrt',
    function(Values: TArray<Double>): Double
    begin
      Result := sqrt(Values[0]);
    end,
    function(Values: TArray<Double>): Integer
    begin
      if (Values[0] < 0) then
        Result := cErrorFxInvalidValue
      else
        Result := cNoError;
    end));

  // Sqr
  AOperation.Add(TOperator.Create(0, 1, 'sqr',
    function(Values: TArray<Double>): Double
    begin
      Result := sqr(Values[0]);
    end));

  // Sum
  AOperation.Add(TOperator.Create(0, -1, 'sum',
    function(Values: TArray<Double>): Double
    begin
      Result := Sum(Values);
    end,
    function(Values: TArray<Double>): Integer
    begin
      if (Length(Values) < 2) then
        Result := cErrorNotEnoughArgs
      else
        Result := cNoError;
    end));

  // Ceil
  AOperation.Add(TOperator.Create(0, 1, 'ceil',
    function(Values: TArray<Double>): Double
    begin
      Result := Ceil(Values[0]);
    end));

  // Floor
  AOperation.Add(TOperator.Create(0, 1, 'floor',
    function(Values: TArray<Double>): Double
    begin
      Result := Floor(Values[0]);
    end));

  // Sign
  AOperation.Add(TOperator.Create(0, 1, 'sign',
    function(Values: TArray<Double>): Double
    begin
      Result := Sign(Values[0]);
    end));

  // Int;
  AOperation.Add(TOperator.Create(0, 1, 'int',
    function(Values: TArray<Double>): Double
    begin
      Result := int(Values[0]);
    end));

  // Frac;
  AOperation.Add(TOperator.Create(0, 1, 'frac',
    function(Values: TArray<Double>): Double
    begin
      Result := frac(Values[0]);
    end));
end;

procedure AddTrigonometry(AOperation: TOperation);
begin
  // sin
  AOperation.Add(TOperator.Create(0, 1, 'sin',
    function(Values: TArray<Double>): Double
    begin
      Result := Sin(Values[0]);
    end));

  // cos
  AOperation.Add(TOperator.Create(0, 1, 'cos',
    function(Values: TArray<Double>): Double
    begin
      Result := Cos(Values[0]);
    end));

  // tan
  AOperation.Add(TOperator.Create(0, 1, 'tan',
    function(Values: TArray<Double>): Double
    begin
      Result := Tan(Values[0]);
    end,
    function(Values: TArray<Double>): Integer
    begin
      if (Values[0] = pi / 2) or (Values[0] = 1.5 * pi) then
        Result := cErrorTan
      else
        Result := cNoError;
    end));

  // arcsin
  AOperation.Add(TOperator.Create(0, 1, 'asin',
    function(Values: TArray<Double>): Double
    begin
      Result := arcsin(Values[0]);
    end,
    function(Values: TArray<Double>): Integer
    begin
      if (Values[0] < -1) or (Values[0] > 1) then
        Result := cErrorFxInvalidValue
      else
        Result := cNoError;
    end));

  // arccos
  AOperation.Add(TOperator.Create(0, 1, 'acos',
    function(Values: TArray<Double>): Double
    begin
      Result := arccos(Values[0]);
    end,
    function(Values: TArray<Double>): Integer
    begin
      if (Values[0] < -1) or (Values[0] > 1) then
        Result := cErrorFxInvalidValue
      else
        Result := cNoError;
    end));

  // arctan
  AOperation.Add(TOperator.Create(0, 1, 'atan',
    function(Values: TArray<Double>): Double
    begin
      Result := arctan(Values[0]);
    end));

  // RadToDeg
  AOperation.Add(TOperator.Create(0, 1, 'radtodeg',
    function(Values: TArray<Double>): Double
    begin
      Result := RadToDeg(Values[0]);
    end));

  // DegToRad
  AOperation.Add(TOperator.Create(0, 1, 'degtorad',
    function(Values: TArray<Double>): Double
    begin
      Result := DegToRad(Values[0]);
    end));
end;

procedure AddTrigonometryDeg(AOperation: TOperation);
begin
  // Sin deg
  AOperation.Add(TOperator.Create(0, 1, 'sind',
    function(Values: TArray<Double>): Double
    begin
      Result := Sin(DegToRad(Values[0]));
    end));
  // Cos deg
  AOperation.Add(TOperator.Create(0, 1, 'cosd',
    function(Values: TArray<Double>): Double
    begin
      Result := Cos(DegToRad(Values[0]));
    end));

  // Tan deg
  AOperation.Add(TOperator.Create(0, 1, 'tand',
    function(Values: TArray<Double>): Double
    begin
      Result := Tan(DegToRad(Values[0]));
    end,
    function(Values: TArray<Double>): Integer
    begin
      if SameValue(DegToRad(Values[0]), pi / 2, 0.0001) or SameValue(DegToRad(Values[0]), 1.5 * pi, 0.0001) then
        Result := cErrorTan
      else
        Result := cNoError;
    end));

  // arcSin deg
  AOperation.Add(TOperator.Create(0, 1, 'asind',
    function(Values: TArray<Double>): Double
    begin
      Result := RadToDeg(arcsin(Values[0]));
    end,
    function(Values: TArray<Double>): Integer
    begin
      if (Values[0] < RadToDeg(-1)) or (Values[0] > RadToDeg(1)) then
        Result := cErrorFxInvalidValue
      else
        Result := cNoError;
    end));

  // arcCos deg
  AOperation.Add(TOperator.Create(0, 1, 'acosd',
    function(Values: TArray<Double>): Double
    begin
      Result := RadToDeg(arccos(Values[0]));
    end,
    function(Values: TArray<Double>): Integer
    begin
      if (Values[0] < RadToDeg(-1)) or (Values[0] > RadToDeg(1)) then
        Result := cErrorFxInvalidValue
      else
        Result := cNoError;
    end));

  // arcTan deg
  AOperation.Add(TOperator.Create(0, 1, 'atand',
    function(Values: TArray<Double>): Double
    begin
      Result := RadToDeg(arctan(Values[0]));
    end));
end;

procedure AddLogarithm(AOperation: TOperation);
begin
  // Ln
  AOperation.Add(TOperator.Create(0, 1, 'ln',
    function(Values: TArray<Double>): Double
    begin
      Result := ln(Values[0]);
    end,
    function(Values: TArray<Double>): Integer
    begin
      if (Values[0] <= 0) then
        Result := cErrorFxInvalidValue
      else
        Result := cNoError;
    end));

  // lnxp1
  AOperation.Add(TOperator.Create(0, 1, 'lnxp1',
    function(Values: TArray<Double>): Double
    begin
      Result := LnXP1(Values[0]);
    end,
    function(Values: TArray<Double>): Integer
    begin
      if (Values[0] <= -1) then
        Result := cErrorFxInvalidValue
      else
        Result := cNoError;
    end));

  // ldexp
  AOperation.Add(TOperator.Create(0, 2, 'ldexp',
    function(Values: TArray<Double>): Double
    begin
      Result := Ldexp(Values[0], round(Values[1]));
    end));

  // Log
  AOperation.Add(TOperator.Create(0, 1, 'log10',
    function(Values: TArray<Double>): Double
    begin
      Result := log10(Values[0]);
    end,
    function(Values: TArray<Double>): Integer
    begin
      if (Values[0] <= 0) then
        Result := cErrorFxInvalidValue
      else
        Result := cNoError;
    end));

  // LogN
  AOperation.Add(TOperator.Create(0, 2, 'logn',
    function(Values: TArray<Double>): Double
    begin
      Result := LogN(Values[0], Values[1]);
    end,
    function(Values: TArray<Double>): Integer
    begin
      if (Values[0] <= 0) or (Values[1] <= 0) or (Log2(Values[0]) = 0) then
        Result := cErrorFxInvalidValue
      else
        Result := cNoError;
    end));

  // Exp
  AOperation.Add(TOperator.Create(0, 1, 'exp',
    function(Values: TArray<Double>): Double
    begin
      Result := exp(Values[0]);
    end));
end;

  function bool2float(val: Boolean): double; inline;
  begin
    if val then
      Result := 1
    else
      Result := 0;
  end;

procedure AddComparisons(AOperation: TOperation);
begin
  AOperation.Add(TOperator.Create(0.9, 2, '>',
    function(Values: TArray<Double>): Double
    begin
      Result := bool2float(Values[0] > Values[1]);
    end));

  AOperation.Add(TOperator.Create(0.9, 2, '>=',
    function(Values: TArray<Double>): Double
    begin
      Result := bool2float(Values[0] >= Values[1]);
    end));

  AOperation.Add(TOperator.Create(0.9, 2, '<',
    function(Values: TArray<Double>): Double
    begin
      Result := bool2float(Values[0] < Values[1]);
    end));

  AOperation.Add(TOperator.Create(0.9, 2, '<=',
    function(Values: TArray<Double>): Double
    begin
      Result := bool2float(Values[0] <= Values[1]);
    end));

  AOperation.Add(TOperator.Create(0.8, 2, '==',
    function(Values: TArray<Double>): Double
    begin
      Result := bool2float(Values[0] = Values[1]);
    end));

  AOperation.Add(TOperator.Create(0.8, 2, '!=',
    function(Values: TArray<Double>): Double
    begin
      Result := bool2float(Values[0] <> Values[1]);
    end));
end;

procedure AddLogic(AOperation: TOperation);
begin
  AOperation.Add(TOperator.Create(0.6, 2, '&&',
    function(ArgStack: TArgStack): Double
    var
      Val0: Double;
    begin
      Val0 := ArgStack[0]();
      if Val0 <> 0 then
        Result := ArgStack[1]()
      else
        Result := Val0;
    end));

  AOperation.Add(TOperator.Create(0.59, 2, '||',
    function(ArgStack: TArgStack): Double
    var
      Val0: Double;
    begin
      Val0 := ArgStack[0]();
      if Val0 <> 0 then
        Result := Val0
      else
        Result := ArgStack[1]();
    end));

  AOperation.Add(TOperator.Create(0, -1, 'if',
    function(ArgStack: TArgStack): Double
    var
      Val0: Double;
    begin
      Val0 := ArgStack[0]();
      if Val0 <> 0 then
        Result := ArgStack[1]()
      else if Length(ArgStack) > 2 then
        Result := ArgStack[2]()
      else
        Result := 0;
    end,
    function(ArgStack: TArgStack): Integer
    begin
      if Length(ArgStack) < 2 then
        Result := cErrorNotEnoughArgs
      else if Length(ArgStack) > 3 then
        Result := cErrorToManyArgs
      else
        Result := cNoError;
    end));

  AOperation.Add(TOperator.Create(2.5, 1, '!',
    function(Values: TArray<Double>): Double
    begin
      Result := bool2float(Values[0] = 0);
    end));
end;

procedure AddAssignment(AOperation: TOperation);
begin
  AOperation.Add(TOperator.Create(0.2, 2, '=',
    function(ArgStack: TArgStack): Double
    begin
      Result := ArgStack[1]();
    end));
end;

{ TParserItem }

constructor TParserItem.Create(aTypeStack: TTypeStack; APos: Integer; aName: string);
begin
  inherited Create;
  FValue     := 0;
  FTypeStack := aTypeStack;
  FName      := aName;
  FTextPos   := APos;
end;

constructor TParserItem.Create(aValue: Double; APos: Integer; aName: string);
begin
  inherited Create;
  FValue     := aValue;
  FTypeStack := tsValue;
  FName      := aName;
  FTextPos   := APos;
end;

constructor TParserItem.Create(aValue: TFunc<Double>; APos: Integer; aName: string);
begin
  inherited Create;
  FValueFunc := aValue;
  FTypeStack := tsValue;
  FName      := aName;
  FTextPos   := APos;
end;

constructor TParserItem.Create(aItem: TParserItem);
begin
  inherited Create;
  Self.Assign(aItem);
end;

function TParserItem.GetIsFunc: Boolean;
begin
  Result := Assigned(FValueFunc);
end;

function TParserItem.GetValue: Double;
begin
  if GetIsFunc then
    Result := FValueFunc
  else
    Result := FValue;
end;

function TParserItem.GetValueFunc: TFunc<Double>;
var
  Value: Double;
begin
  if GetIsFunc then
    Result := FValueFunc
  else begin
    Value := FValue;
    Result := function: Double begin Result := Value end;
  end;
end;

procedure TParserItem.Assign(Source: TObject);
begin
  if Source is TParserItem then
  begin
    FValue          := TParserItem(Source).FValue;
    FValueFunc      := TParserItem(Source).FValueFunc;
    FTypeStack      := TParserItem(Source).FTypeStack;
    FName           := TParserItem(Source).FName;
    FArgumentsCount := TParserItem(Source).FArgumentsCount;
    FTextPos        := TParserItem(Source).FTextPos;
  end;
  inherited;
end;

procedure TParserItem.Read(S: TStream);
var
  c     : Integer;
  StrBuf: TBytes;
begin
  S.ReadBuffer(FValue, SizeOf(Double));
  S.ReadBuffer(FTypeStack, SizeOf(TTypeStack));

  S.ReadBuffer(c, SizeOf(Integer));
  SetLength(StrBuf, c);
  S.ReadBuffer(StrBuf, c);
  FName := TEncoding.UTF8.GetString(StrBuf);

  S.ReadBuffer(FArgumentsCount, SizeOf(Integer));
end;

procedure TParserItem.Write(S: TStream);
var
  c     : Integer;
  StrBuf: TBytes;
begin
  if GetIsFunc then
    raise Exception.Create('Cannot write value func to stream');

  S.WriteBuffer(FValue, SizeOf(Double));
  S.WriteBuffer(FTypeStack, SizeOf(TTypeStack));

  StrBuf := TEncoding.UTF8.GetBytes(FName);
  c      := Length(StrBuf);
  S.WriteBuffer(c, SizeOf(Integer));
  S.WriteBuffer(StrBuf, c);

  S.WriteBuffer(FArgumentsCount, SizeOf(Integer));
end;

procedure ClearAndFreeStack(S: TStack<TParserItem>);
begin
  while S.Count > 0 do
    S.Pop.Free;
end;

{ TError }

procedure TError.Clear;
begin
  FCode     := cNoError;
  FPosition := -1;
  FName     := '';
end;

constructor TError.Create(ACode, APosition: Integer; AName: string);
begin
  FCode     := ACode;
  FPosition := APosition;
  FName     := AName;
end;

function TError.IsNoError: Boolean;
begin
  Result := FCode = cNoError;
end;

function TError.ToString: string;
begin
  case FCode of
    cNoError:
      Result := '';

    cInternalError:
      Result := 'Cannot parse';

    cErrorInvalidChar:
      Result := 'Invalid char ''%0:s'' at position %1:d';
    cErrorUnknownName:
      Result := 'Unknown function or variable ''%0:s'' at position %1:d';
    cErrorInvalidFloat:
      Result := 'Invalid float number ''%0:s'' at position %1:d';
    cErrorOperator:
      Result := 'Operator ''%0:s'' cannot be placed here at position %1:d';
    cErrorInvalidOperator:
      Result := 'Invalid operator ''%0:s'' at position %1:d';
    cErrorNotEnoughArgs:
      Result := 'Not enough arguments or operands at position %1:d';
    cErrorSeparatorNeedArgument:
      Result := 'Missing argument after separator at position %1:d';
    cErrorMissingLeftBrackets:
      Result := 'Missing at least one left Bracket at position %1:d';
    cErrorMissingRightBrackets:
      Result := 'Missing at least one right Bracket at position %1:d';
    cErrorLeftBracket:
      Result := 'Left Bracket cannot be placed here at position %1:d';
    cErrorRightBracket:
      Result := 'Right Bracket cannot be placed here at position %1:d';
    cErrorSeparator:
      Result := 'Separator cannot be placed here at position %1:d';
    cErrorOperatorNeedArgument:
      Result := 'Operator must be followed by argument at position %1:d';
    cErrorAssignmentError:
      Result := 'Invalid left-hand side in assignment at position %1:d';

    cErrorCalc:
      Result := 'Invalid operation at position %1:d';
    cErrorDivByZero:
      Result := 'Division by zero at position %1:d';
    cErrorPower:
      Result := 'Invalid use of power function at position %1:d';
    cErrorFxInvalidValue:
      Result := 'Invalid parameter value for function at position %1:d';
    cErrorTan:
      Result := 'Invalid parameter value for tangent-function at position %1:d';
  end;

  Result := Format(Result, [FName, FPosition]);
end;

end.
