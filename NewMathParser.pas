// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

/// Viel ge�ndert von Jens Biermann am 07.02.2012
/// Viel ge�ndert von Jens Biermann am 29.01.2015
/// �nderungen von Jens Biermann am 23.08.2016
/// TParserStack to TList and Bugfix 10.09.2016

unit NewMathParser;

interface

uses System.Classes, System.Generics.Collections, NewMathParser.Oper, System.SysUtils;

type
  TNotifyError = Procedure(Sender: TObject; Error: TError) of object;

  TParserStack = class(TObjectList<TParserItem>)
  strict private
  public
    procedure Clear(const ST: TTypeStack); overload;
    procedure SetArgCount;
    function ArgCount(const SI: TParserItem): Integer;
    function CountType(const ST: TTypeStack): Integer; overload;
    function Contains(const ST: TTypeStack): Boolean;
    function First(const ST: TTypeStack): TParserItem; overload;
    function Last(const ST: TTypeStack): TParserItem; overload;
  end;

  TProzessbasis = class(TObject)
  strict protected
    FStack     : TParserStack;
    FError     : PError;
    FOperations: TOperation;
  public
    constructor Create(AStack: TParserStack; AOperations: TOperation; AError: PError);
    // destructor Destroy; override;
    procedure Prozess; virtual; abstract;
    property Error: PError read FError;
  end;

  TValidate = class(TProzessbasis)
  strict private
    procedure ValidateRightBracket(const Pos: Integer);
    procedure ValidateSeparator(const Pos: Integer);
    procedure ValidateOperator(const Pos: Integer);
    procedure CheckBracketError;
    procedure Loop;
    procedure CleanPlusMinus;
    procedure InsertMulti;
    procedure CountArg;
    procedure CheckError;
  public
    procedure Prozess; override;
  end;

  TPriority = class(TProzessbasis)
  strict private
    FTmpStack: TStack<TParserItem>;
    FPStack  : TStack<TParserItem>;
    procedure MoveRightBracket(Current: TParserItem);
    procedure MoveSeparator(Current: TParserItem);
    procedure MoveOperator(Current: TParserItem);
    procedure CreateNewStack;
  public
    constructor Create(AStack: TParserStack; AOperations: TOperation; AError: PError);
    destructor Destroy; override;
    procedure Prozess; override;
  end;

  TParser = class(TObject)
  strict private
    FStack        : TList<TParserItem>;
    FError        : PError;
    FOperations   : TOperation;
    FParsePosition: Integer;
    FExpression   : string;
    procedure ParseExponent;
    procedure ParseNumbers;
    procedure ParseFunctions;
    procedure Parse;
    function ItemNameToStackType(AName: string): TTypeStack;
  private
    procedure ParseOperators;
  public
    constructor Create(AOperations: TOperation; AError: PError);
    destructor Destroy; override;
    function ExpressionToStack(const Expression: string): TArray<TParserItem>;
  end;

  TVar = record
  private
    FValue    : Double;
    FValueFunc: TFunc<Double>;
    FName     : string;
    function GetIsFunc: Boolean;
    function GetValue: Double;
    procedure SetValue(const Value: Double);
  public
    constructor Create(aName: string; aValue: Double); overload;
    constructor Create(aName: string; aValue: TFunc<Double>); overload;
    property Name: string read FName write FName;
    property IsFunc: Boolean read GetIsFunc;
  public
    class operator Implicit(a: Double): TVar; overload; inline;
    class operator Implicit(a: TFunc<Double>): TVar; overload; inline;
    class operator Implicit(a: TVar): Double; overload; inline;
  end;

  TVariables = class(TDictionary<string, TVar>)
  private
    function GetItem(const Key: string): TVar;
    procedure SetItem(const Key: string; const Value: TVar);
  public
    constructor Create(FillDefaults: boolean = true); reintroduce;
    procedure Add(Name: string; Value: Double); overload;
    procedure Add(Name: string; Value: TFunc<Double>); overload;
    property Items[const Key: string]: TVar read GetItem write SetItem; default;
  end;

  TCalculator = class(TObject)
  strict private
    FVariables  : TVariables;
    FResultStack: TStack<TParserItem>;
    FError      : PError;
    FOperations : TOperation;
    procedure StackToResult_Operation(ACurrent: TParserItem);
    procedure StackToResult(const AStack: TArray<TParserItem>);
    procedure StackToResult_Variable(Current: TParserItem);
  public
    constructor Create(AOperations: TOperation; AVariables: TVariables; AError: PError);
    destructor Destroy; override;
    procedure MakeResultStack(const AStack: TArray<TParserItem>);
    function Result: Double;
  end;

  TMathParser = class(TObject)
  private
    FResult    : Double;
    FError     : TError;
    FMainStack : TParserStack;
    FExpression: string;
    FOnError   : TNotifyError;
    FVariables : TVariables;
    FOwnsVariables: Boolean;
    FCalculator: TCalculator;
    FIsToCalc  : Boolean;
    FValidate  : TValidate;
    FParser    : TParser;
    FPriority  : TPriority;
    FOperations: TOperation;
    function GetParserResult: Double;
    procedure SetExpression(const Value: string);
    procedure DoError(AError: TError);
    procedure CreateStack;
  public
    constructor Create; overload;
    constructor Create(aVariables: TVariables); overload;
    destructor Destroy; override;
    function GetLastError: TError; deprecated 'use Error';
    // dont use stream! Is quicker to save the Expressionstring
    procedure SaveToStream(S: TStream);
    procedure LoadFromStream(S: TStream);
    property Expression: string read FExpression write SetExpression;
    property ParserResult: Double read GetParserResult;
    property Variables: TVariables read FVariables write FVariables;
    property OwnsVariables: boolean read FOwnsVariables write FOwnsVariables;
    property OnError: TNotifyError read FOnError write FOnError;
    property Error: TError read FError;
  end;

implementation

var
  LocalFormatSettings: TFormatSettings;

constructor TMathParser.Create;
var
  aVariables: TVariables;
begin
  aVariables  := TVariables.Create;
  Create(aVariables);
  FOwnsVariables := true;
end;

constructor TMathParser.Create(aVariables: TVariables);
begin
  inherited Create;
  FExpression := '';
  FError.Clear;
  FIsToCalc   := False;
  FOperations := TOperation.Create;
  FMainStack  := TParserStack.Create;
  FVariables  := aVariables;
  FCalculator := TCalculator.Create(FOperations, FVariables, @FError);

  AddOperation(FOperations);
  AddMath(FOperations);
  AddTrigonometry(FOperations);
  AddTrigonometryDeg(FOperations);
  AddLogarithm(FOperations);
  AddComparisons(FOperations);
  AddLogic(FOperations);
  AddAssignment(FOperations);

  FValidate := TValidate.Create(FMainStack, FOperations, @FError);
  FParser   := TParser.Create(FOperations, @FError);
  FPriority := TPriority.Create(FMainStack, FOperations, @FError);
end;

destructor TMathParser.Destroy;
begin
  FPriority.Free;
  FParser.Free;
  FValidate.Free;

  FCalculator.Free;
  FMainStack.Free;

  if FOwnsVariables then
    FVariables.Free;
  FOperations.Free;
  inherited;
end;

procedure TMathParser.DoError(AError: TError);
begin
  if not AError.IsNoError then
    if Assigned(FOnError) then
      FOnError(Self, FError)
    else
      raise EParseError.Create(FError.ToString);
end;

procedure TMathParser.SetExpression(const Value: string);
begin
  if not SameStr(FExpression, Value) then
  begin
    FResult     := 0;
    FExpression := Value;
    FError.Clear;
    FIsToCalc := True;
    if (FExpression.Length > 0) then
      CreateStack;
  end;
end;

function TMathParser.GetParserResult: Double;
begin
  Result := 0;

  if FIsToCalc then
  begin
    FCalculator.MakeResultStack(FMainStack.ToArray);
    DoError(FError);
    FIsToCalc := False;
  end;

  if FError.IsNoError then begin
    Result := FCalculator.Result;
    DoError(FError);
  end;
end;

procedure TMathParser.SaveToStream(S: TStream);
var
  c     : Integer;
  SI    : TParserItem;
  StrBuf: TBytes;
begin
  StrBuf := TEncoding.UTF8.GetBytes(FExpression);
  c      := Length(StrBuf);
  S.WriteBuffer(c, SizeOf(Integer));
  S.WriteBuffer(StrBuf, c);

  S.WriteBuffer(FError, SizeOf(Integer));
  c := FMainStack.Count;
  S.WriteBuffer(c, SizeOf(Integer));
  for SI in FMainStack do
    SI.Write(S);
end;

procedure TMathParser.LoadFromStream(S: TStream);
var
  c     : Integer;
  i     : Integer;
  SI    : TParserItem;
  StrBuf: TBytes;
  Exp   : string;
begin
  S.Position := 0;

  S.ReadBuffer(c, SizeOf(Integer));
  SetLength(StrBuf, c);
  S.ReadBuffer(StrBuf, c);
  Exp := TEncoding.UTF8.GetString(StrBuf);
  if not SameStr(Exp, FExpression) then
  begin
    FExpression := Exp;
    FResult     := 0;
    FIsToCalc   := True;
  end;

  S.ReadBuffer(FError, SizeOf(Integer));
  FMainStack.Clear;

  S.ReadBuffer(c, SizeOf(Integer));
  for i := 0 to c - 1 do
  begin
    SI := TParserItem.Create;
    SI.Read(S);
    FMainStack.Add(SI);
  end;
end;

procedure TMathParser.CreateStack;
begin
  FMainStack.Clear;
  FMainStack.AddRange(FParser.ExpressionToStack(FExpression));
  FValidate.Prozess;
  FPriority.Prozess;
  // FMainStack.Clear(tsLeftBracket);
  // FMainStack.Clear(tsRightBracket);
  // FMainStack.Clear(tsSeparator);
  DoError(FError);
end;

function TMathParser.GetLastError: TError;
begin
  Result := FError;
end;

{ TPostProzess_Validate }

procedure TValidate.Prozess;
begin
  if FError^.IsNoError then
  begin
    CheckBracketError;
    if FError.IsNoError then
      FStack.SetArgCount;
    CleanPlusMinus;
    InsertMulti;
    Loop;
    if FError.IsNoError then
    begin
      CountArg;
      CheckError;
    end;
  end;
end;

procedure TValidate.CheckError;
var
  i, c: Integer;
begin
  for i := 0 to FStack.Count - 1 do
    if (FError^.IsNoError) and (FStack[i].TypeStack in [tsFunction, tsOperator]) then
    begin
      c := FOperations[FStack[i].Name].Arguments;
      if (FStack[i].ArgumentsCount > c) and (c > -1) then
      begin
        FError^.Code     := cErrorToManyArgs;
        FError^.Position := FStack[i].TextPos;
      end

      else if (FStack[i].ArgumentsCount < c) or (c > -1) and (FStack[i].ArgumentsCount = 0) then
      begin
        FError^.Code     := cErrorNotEnoughArgs;
        FError^.Position := FStack[i].TextPos;
      end

      else if (i < FStack.Count - 2) and (FStack[i + 1].TypeStack = tsLeftBracket) and
        (FStack[i + 2].TypeStack = tsRightBracket) then
      begin
        FStack[i].ArgumentsCount := 0;
        FError^.Code             := cErrorNotEnoughArgs;
        FError^.Position         := FStack[i].TextPos;
      end
    end;
end;

procedure TValidate.CountArg;
var
  iSS: TParserItem;
begin
  for iSS in FStack do
    if iSS.TypeStack = tsOperator then
      iSS.ArgumentsCount := FOperations[iSS.Name].Arguments;
end;

procedure TValidate.CleanPlusMinus;
const
  STypes = [tsOperator, tsLeftBracket, tsSeparator];
var
  i: Integer;
begin
  for i := FStack.Count - 1 downto 0 do
    if (i = 0) or (FStack[i - 1].TypeStack in STypes) then
      if SameStr(FStack[i].Name, '+') then
        FStack.Extract(FStack[i]).Free
      else if SameStr(FStack[i].Name, '-') then
        FStack[i].Name := 'neg';
end;

procedure TValidate.CheckBracketError;
var
  LeftBracketCount : Integer;
  RightBracketCount: Integer;
  iSS              : TParserItem;
begin
  LeftBracketCount  := FStack.CountType(tsLeftBracket);
  RightBracketCount := FStack.CountType(tsRightBracket);

  if LeftBracketCount > RightBracketCount then
  begin
    FError^.Code     := cErrorMissingRightBrackets;
    iSS              := FStack.First(tsLeftBracket);
    FError^.Position := iSS.TextPos;
  end

  else if LeftBracketCount < RightBracketCount then
  begin
    FError^.Code     := cErrorMissingLeftBrackets;
    iSS              := FStack.Last(tsRightBracket);
    FError^.Position := iSS.TextPos;
  end;
end;

procedure TValidate.InsertMulti;
const
  Types1 = [tsLeftBracket, tsValue, tsVariable, tsFunction];
  Types2 = [tsValue, tsVariable, tsRightBracket];
var
  i: Integer;
begin
  for i := FStack.Count - 2 downto 0 do
    if (FStack[i].TypeStack in Types2) and (FStack[i + 1].TypeStack in Types1) then
      FStack.Insert(i + 1, TParserItem.Create(tsOperator, FStack[i].TextPos, '*'));
end;

procedure TValidate.Loop;
var
  i: Integer;
begin
  i := 0;
  while (FError^.IsNoError) and (i < FStack.Count) do
  begin
    case FStack[i].TypeStack of
      tsRightBracket:
        ValidateRightBracket(i);

      tsSeparator:
        ValidateSeparator(i);

      tsOperator:
        ValidateOperator(i);
    end;
    Inc(i);
  end;
end;

procedure TValidate.ValidateOperator(const Pos: Integer);
begin
  if (Pos = 0) or (FStack[Pos - 1].TypeStack in [tsOperator, tsLeftBracket, tsSeparator]) then
  begin
    if (FStack[Pos].Name.Length >= 1) and CharInSet(FStack[Pos].Name[1], FOperations.OpChars-['-', '+', '!']) then
    begin
      FError^.Code     := cErrorOperator;
      FError^.Position := FStack[Pos].TextPos;
      FError^.Name     := FStack[Pos].Name;
    end;
  end

  else if (Pos = FStack.Count - 1) then
  begin
    FError^.Code     := cErrorOperatorNeedArgument;
    FError^.Position := FStack[Pos].TextPos;
  end;

  if (FStack[Pos].Name = '=') and ((FStack[Pos - 1].TypeStack <> tsVariable)
  or ((Pos > 1) and not (FStack[Pos - 2].TypeStack in [tsLeftBracket, tsSeparator]))) then
  begin
    FError^.Code     := cErrorAssignmentError;
    FError^.Position := FStack[Pos].TextPos;
  end;
end;

procedure TValidate.ValidateRightBracket(const Pos: Integer);
begin
  if (Pos > 0) and (FStack[Pos - 1].TypeStack in [tsFunction, tsOperator, tsSeparator]) then
  begin
    FError^.Code     := cErrorRightBracket;
    FError^.Position := FStack[Pos].TextPos;
  end;
end;

procedure TValidate.ValidateSeparator(const Pos: Integer);
begin
  if Pos = 0 then
  begin
    FError^.Code     := cErrorSeparator;
    FError^.Position := FStack[Pos].TextPos;
  end
  else
    case FStack[Pos - 1].TypeStack of
      tsSeparator:
        begin
          FError^.Code     := cErrorSeparatorNeedArgument;
          FError^.Position := FStack[Pos].TextPos;
        end;
      tsOperator, tsLeftBracket:
        begin
          FError^.Code     := cErrorSeparator;
          FError^.Position := FStack[Pos].TextPos;
        end;
    end;
end;

{ TProzessbasis }

constructor TProzessbasis.Create(AStack: TParserStack; AOperations: TOperation; AError: PError);
begin
  inherited Create;
  FOperations := AOperations;
  FStack      := AStack;
  FError      := AError;
end;

{ TPraeProzess }

constructor TParser.Create(AOperations: TOperation; AError: PError);
begin
  inherited Create;
  FOperations := AOperations;
  FStack      := TList<TParserItem>.Create;
  FError      := AError;
end;

destructor TParser.Destroy;
begin
  FStack.Free;
  inherited;
end;

procedure TParser.ParseOperators;
var
  S : string;
  Op: TOperator;

  function OperationChars: string;
  var
    i: Integer;
  begin
    Result := '';
    for i  := FParsePosition to Length(FExpression) do
      if CharInSet(FExpression[i], FOperations.OpChars) then
        Result := Result + FExpression[i]
      else
        Break;
  end;

begin
  S := OperationChars;
  while Length(S) > 0 do begin
    Op := FOperations[S];
    if Assigned(Op) then begin
      FStack.Add(TParserItem.Create(ItemNameToStackType(Op.Name), FParsePosition, Op.Name));
      FParsePosition := FParsePosition + Length(S);
      Break;
    end;
    S := Copy(S, 0, S.Length-1);
  end;

  if Length(S) = 0 then begin
    FError^.Code     := cErrorInvalidOperator;
    FError^.Position := FParsePosition;
    FError^.Name     := OperationChars;
  end;
end;

procedure TParser.ParseFunctions;
var
  S : string;
  Op: TOperator;

  function FunctionOfExpression: string;
  var
    i: Integer;
  begin
    Result := '';
    for i  := FParsePosition to Length(FExpression) do
      if CharInSet(FExpression[i], Letters + Numbers + ['_']) then
        Result := Result + FExpression[i]
      else
        Break;
  end;

begin
  S := FunctionOfExpression;
  if Length(S) > 0 then
  begin
    Op := FOperations[S];
    if Assigned(Op) then
      FStack.Add(TParserItem.Create(ItemNameToStackType(Op.Name), FParsePosition, Op.Name))
    else
      FStack.Add(TParserItem.Create(tsVariable, FParsePosition, S));

    FParsePosition := FParsePosition + Length(S);
  end;
end;

procedure TParser.ParseNumbers;
var
  s: string;
  v: Double;

  function NumberInString: string;
  var
    i: Integer;
  begin
    Result := '';
    for i  := FParsePosition to Length(FExpression) do
      if CharInSet(FExpression[i], Numbers) then
        Result := Result + FExpression[i]
      else if FExpression[i] = LocalFormatSettings.DecimalSeparator then
        Result := Result + LocalFormatSettings.DecimalSeparator
      else
        Break;
  end;

begin
  s              := NumberInString;
  FParsePosition := FParsePosition + Length(s);

  if TryStrToFloat(s, v, LocalFormatSettings) then
    FStack.Add(TParserItem.Create(v, FParsePosition, ''))
  else
  begin
    FError^.Code     := cErrorInvalidFloat;
    FError^.Position := FParsePosition;
    FError^.Name     := s;
  end;
end;

procedure TParser.Parse;
var
  L: Integer;
begin
  FParsePosition := 1;
  ParseExponent;
  L := Length(FExpression);

  while FError^.IsNoError and (FParsePosition <= L) do
    with FStack do
    begin
      case FExpression[FParsePosition] of
        '(', '{', '[', ')', '}', ']':
          begin
            Add(TParserItem.Create(ItemNameToStackType(FExpression[FParsePosition]), FParsePosition, FExpression[FParsePosition]));
            Inc(FParsePosition);
          end;

        ';', ',':
          begin
            Add(TParserItem.Create(tsSeparator, FParsePosition, ''));
            Inc(FParsePosition);
          end;

        ' ':
          Inc(FParsePosition);

      else
        if CharInSet(FExpression[FParsePosition], ['_'] + Letters) then begin
          ParseFunctions;
        end else
        if CharInSet(FExpression[FParsePosition], ['.'] + Numbers) then begin
          ParseNumbers;
        end else if CharInSet(FExpression[FParsePosition], FOperations.OpChars) then begin
          ParseOperators;
        end else begin
          FError^.Code     := cErrorInvalidChar;
          FError^.Position := FParsePosition;
          FError^.Name     := FExpression[FParsePosition];
        end;
      end;
    end;
end;

procedure TParser.ParseExponent;
var
  L: Integer;
  i: Integer;
begin
  L     := Length(FExpression);
  for i := 2 to L - 1 do
    if FExpression[i] = 'e' then
    begin
      if CharInSet(FExpression[i - 1], Numbers + [')', ']']) and
        (CharInSet(FExpression[i + 1], Numbers) or CharInSet(FExpression[i + 1], ['+', '-']) and
        CharInSet(FExpression[i + 2], Numbers)) then
      begin
        Delete(FExpression, i, 1);
        Insert('*10^', FExpression, i);
      end;
    end;
end;

function TParser.ExpressionToStack(const Expression: string): TArray<TParserItem>;
begin
  FExpression := Expression.ToLower;
  FStack.Clear;
  Parse;
  Result := FStack.ToArray;
end;

function TParser.ItemNameToStackType(AName: string): TTypeStack;
begin
  if (Length(AName) = 1) and (AName[1] = '(') then
    Result := tsLeftBracket
  else if (Length(AName) = 1) and (AName[1] = ')') then
    Result := tsRightBracket
  else if CharInSet(AName[1], FOperations.OpChars) and Assigned(FOperations[AName]) then
    Result := tsOperator
  else
    Result := tsFunction;
end;

{ TPostProzess_Priority }

constructor TPriority.Create(AStack: TParserStack; AOperations: TOperation; AError: PError);
begin
  inherited;
  FPStack   := TStack<TParserItem>.Create;
  FTmpStack := TStack<TParserItem>.Create;
end;

destructor TPriority.Destroy;
begin
  FTmpStack.Free;
  FPStack.Free;
  inherited;
end;

procedure TPriority.Prozess;
var
  iSS: TParserItem;
begin
  if FError^.IsNoError then
  begin
    FTmpStack.Clear;
    FPStack.Clear;
    for iSS in FStack do
    begin
      case iSS.TypeStack of
        tsValue, tsVariable:
          FPStack.Push(iSS);

        tsFunction, tsLeftBracket:
          FTmpStack.Push(iSS);

        tsRightBracket:
          MoveRightBracket(iSS);

        tsSeparator:
          MoveSeparator(iSS);

        tsOperator:
          MoveOperator(iSS);
      end;
    end;
    CreateNewStack;
  end;
end;

procedure TPriority.CreateNewStack;
begin
  while FTmpStack.Count > 0 do
    FPStack.Push(FTmpStack.Pop);

  FStack.OwnsObjects := False;
  try
    FStack.Clear;
  finally
    FStack.OwnsObjects := True;
  end;
  FStack.AddRange(FPStack);
end;

procedure TPriority.MoveOperator(Current: TParserItem);
var
  Prio: Double;
begin
  Prio := FOperations[Current.Name].Priority;
  with FTmpStack do
    while (Count > 0) and (Peek.TypeStack = tsOperator)
    and ((Prio < FOperations[Peek.Name].Priority) or ((Prio <= FOperations[Peek.Name].Priority) and (FOperations[Peek.Name].Arguments <> 1))) do
      FPStack.Push(FTmpStack.Pop);
  FTmpStack.Push(Current);
end;

procedure TPriority.MoveSeparator(Current: TParserItem);
begin
  while (FTmpStack.Count > 0) and (FTmpStack.Peek.TypeStack <> tsLeftBracket) do
    FPStack.Push(FTmpStack.Pop);
  Current.Free;
end;

procedure TPriority.MoveRightBracket(Current: TParserItem);
begin
  while (FTmpStack.Count > 0) and (FTmpStack.Peek.TypeStack <> tsLeftBracket) do
    FPStack.Push(FTmpStack.Pop);
  FTmpStack.Pop.Free;
  if (FTmpStack.Count > 0) and (FTmpStack.Peek.TypeStack = tsFunction) then
    FPStack.Push(FTmpStack.Pop);
  Current.Free;
end;

{ TVar }

constructor TVar.Create(aName: string; aValue: TFunc<Double>);
begin
  FName      := aName;
  FValueFunc := aValue;
end;

constructor TVar.Create(aName: string; aValue: Double);
begin
  FName  := aName;
  FValue := aValue;
end;

function TVar.GetIsFunc: Boolean;
begin
  Result := Assigned(FValueFunc);
end;

function TVar.GetValue: Double;
begin
  if GetIsFunc then
    Result := FValueFunc
  else
    Result := FValue;
end;

class operator TVar.Implicit(a: TFunc<Double>): TVar;
begin
  Result.FValueFunc := a;
end;

class operator TVar.Implicit(a: Double): TVar;
begin
  Result.SetValue(a);
end;

class operator TVar.Implicit(a: TVar): Double;
begin
  Result := a.GetValue;
end;

procedure TVar.SetValue(const Value: Double);
begin
  if GetIsFunc then
    raise Exception.Create('Error: Value is a function')
  else
    FValue := Value;
end;

{ TVariables }

procedure TVariables.Add(Name: string; Value: Double);
begin
  inherited AddOrSetValue(Name.ToUpper, TVar.Create(Name, Value));
end;

procedure TVariables.Add(Name: string; Value: TFunc<Double>);
begin
  inherited AddOrSetValue(Name.ToUpper, TVar.Create(Name, Value));
end;

constructor TVariables.Create(FillDefaults: boolean);
begin
  inherited Create;

  if FillDefaults then begin
    Add('pi', Pi);
    Add('true', 1);
    Add('false', 0);
  end;
end;

function TVariables.GetItem(const Key: string): TVar;
begin
  Result := inherited Items[Key.ToUpper];
end;

procedure TVariables.SetItem(const Key: string; const Value: TVar);
begin
  AddOrSetValue(Key.ToUpper, Value);
end;

{ TCalculator }

constructor TCalculator.Create(AOperations: TOperation; AVariables: TVariables; AError: PError);
begin
  inherited Create;
  FOperations  := AOperations;
  FVariables   := AVariables;
  FError       := AError;
  FResultStack := TStack<TParserItem>.Create;
end;

destructor TCalculator.Destroy;
begin
  ClearAndFreeStack(FResultStack);
  FResultStack.Free;
  inherited;
end;

procedure TCalculator.StackToResult(const AStack: TArray<TParserItem>);
var
  Current: TParserItem;
begin
  for Current in AStack do
    if FError^.IsNoError then
      case Current.TypeStack of
        tsValue:
          FResultStack.Push(TParserItem.Create(Current));

        tsVariable:
          StackToResult_Variable(Current);

        tsOperator, tsFunction:
          StackToResult_Operation(Current);
      end;
end;

procedure TCalculator.StackToResult_Operation(ACurrent: TParserItem);
var
  ArgStack: TArgStack;
  O    : TOperator;
  i    : Integer;
  Error: Integer;
  LeftVarName: string;
begin
  LeftVarName := '';

  SetLength(ArgStack, ACurrent.ArgumentsCount);
  for i := ACurrent.ArgumentsCount - 1 downto 0 do with FResultStack.Pop do begin
    ArgStack[i] := ValueFunc;
    if i = 0 then
      LeftVarName := Name;
    Free;
  end;

  O     := FOperations[ACurrent.Name];
  FResultStack.Push(TParserItem.Create(function: double
  begin
    Error := O.Error(ArgStack);
    if Error = cNoError then
    begin
      Result := O.Func(ArgStack);
      if (ACurrent.Name = '=') then
        FVariables.Add(LeftVarName.ToUpper, Result);
    end else
    begin
      Result := 0;
      FError^.Code     := Error;
      FError^.Position := ACurrent.TextPos;
    end;
  end, ACurrent.TextPos, ACurrent.Name));
end;

procedure TCalculator.MakeResultStack(const AStack: TArray<TParserItem>);
begin
  ClearAndFreeStack(FResultStack);
  StackToResult(AStack);
end;

procedure TCalculator.StackToResult_Variable(Current: TParserItem);
var
  Value: TVar;
begin
  FResultStack.Push(TParserItem.Create(function: double begin
    if FVariables.TryGetValue(Current.Name.ToUpper, Value) then
      Result := Value
    else
    begin
      FError^.Code     := cErrorUnknownName;
      FError^.Position := Current.TextPos;
      FError^.Name     := Current.Name;
    end;
  end, Current.TextPos, Current.Name))
end;

function TCalculator.Result: Double;
begin
  Result := 0;
  if (FResultStack.Count = 1) and FError^.IsNoError then
  begin
    Result := FResultStack.Peek.Value;
  end
  else if FError^.IsNoError then
  begin
    FError^.Code     := cInternalError;
    FError^.Position := -1;
  end;
end;

{ TParserStack }

function TParserStack.ArgCount(const SI: TParserItem): Integer;
var
  Pos: Integer;
  c  : Integer;
  i  : Integer;
begin
  Pos    := IndexOf(SI);
  c      := 0;
  Result := 0;
  for i  := Pos + 1 to Count - 1 do
  begin
    case Self[i].TypeStack of
      tsSeparator:
        if c = 1 then
          Inc(Result);
      tsLeftBracket:
        Inc(c);
      tsRightBracket:
        begin
          if c = 1 then
          begin
            Inc(Result);
            Break;
          end;
          Dec(c);
        end;
    end;
  end;
end;

procedure TParserStack.Clear(const ST: TTypeStack);
var
  i: Integer;
begin
  for i := Count - 1 downto 0 do
    if Self[i].TypeStack = ST then
      Delete(i);
end;

function TParserStack.Contains(const ST: TTypeStack): Boolean;
var
  iItem: TParserItem;
begin
  for iItem in Self do
    if iItem.TypeStack = ST then
      Exit(True);
  Result := False;
end;

function TParserStack.CountType(const ST: TTypeStack): Integer;
var
  iItems: TParserItem;
begin
  Result := 0;
  for iItems in Self do
    if iItems.TypeStack = ST then
      Inc(Result);
end;

function TParserStack.First(const ST: TTypeStack): TParserItem;
var
  iItems: TParserItem;
begin
  for iItems in Self do
    if iItems.TypeStack = ST then
      Exit(iItems);
  Result := nil;
end;

function TParserStack.Last(const ST: TTypeStack): TParserItem;
var
  i: Integer;
begin
  for i := Self.Count - 1 downto 0 do
    if Self[i].TypeStack = ST then
      Exit(Self[i]);
  Result := nil;
end;

procedure TParserStack.SetArgCount;
var
  iItems: TParserItem;
begin
  for iItems in Self do
    if iItems.TypeStack = tsFunction then
      iItems.ArgumentsCount := ArgCount(iItems);
end;

initialization
  LocalFormatSettings := TFormatSettings.Create;
  LocalFormatSettings.DecimalSeparator := '.';
  LocalFormatSettings.ThousandSeparator := ',';

finalization

end.
