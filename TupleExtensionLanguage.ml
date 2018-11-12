(*Exceptions*)
exception EmptyEnvException;;
exception TypeError;;
exception UnboundVariable;;
exception OutOfBound;;
exception InvalidOperand;;


type ide = string;;
type integer = int;;


type bval =
	|Tint of integer
	|Tbool of bool
	|Tuple of tuple
and tuple =
	|()
	|Add of bval list
and exp =
	|Ide of ide
	|Bval of bval
	|Fval of ide * exp
	|And of exp * exp
	|Or of exp * exp
	|Not of exp
	|Sum of exp * exp
	|Mul of exp * exp
	|Diff of exp * exp
	|Div of exp * exp
	|Mod of exp
	|In of exp * tuple
	|IsEmpty of tuple
	|Slice of tuple * exp * exp
	|Access of tuple * exp
	|For of ide * tuple * exp
	|Appl of ide * exp
	|Ifthenelse of exp * exp * exp
	|LetIn of ide * exp * exp;;



let rec typecheck(x:exp) = match x with
	|Ide(_) -> Ide "ide"
	|Bval(Tbool _ )-> Ide "tbool"
	|Bval(Tint _ )-> Ide "tint"
	|Fval(_,_) -> Ide "fval"
	|Bval(Tuple _)-> Ide "tuple"
	|And(_,_) ->Ide "tbool"
	|Or(_,_) ->Ide "tbool"
	|Not(_) ->Ide "tbool"
	|Sum(_,_)-> Ide "tint"
	|Mul(_,_)-> Ide "tint"
	|Diff(_,_)-> Ide "tint"
	|Div(_,_)-> Ide "tint"
	|Mod(_) -> Ide "tint"
	|In(_) -> Ide "tbool"
	|IsEmpty(_) -> Ide "tbool"
	|Slice(_) -> Ide "tuple"
	|Access(y,x) -> typecheck x
	|For(_,_,_) -> Ide "tuple";;


(*Create an empty environment*)
let env = ref [];;
let funenv = ref [];;

(*binding function*)
let bind ( (ides:ide),(value:exp)) = env := (ides,value)::!env;;

(*Binding function for f as (name)->(param,body,funenv)*)
let funBind ( (name:ide), (param:ide), (body:exp)) = funenv := (name,param,body,(!env))::!funenv;;

let decFun (name:ide) (fval:exp) = match fval with
	|Fval(param,body) -> funBind(name,param,body)
	| _ -> failwith ("Use: ide + Fval(param,boby)");;

(*Pop from environment*)
let pop env= match !env with
	[] -> failwith "Environment is Empty"
	|x::xs -> env := xs;;

let evalBval y= match y with
	|Bval x -> x
	|_ -> failwith "x is not a bval type";;

let evalToTuple y = match y with
	|Tuple x -> x
	|_ -> failwith "x is not a tuple type";;

let rec eval ((exp:exp), env) =
 	match exp with
  		|Ide x -> (match env with
  			|[] -> failwith (" "^x^" not bound")
 			|(ide1,(val1:exp))::env0 -> if x = ide1 then val1 else (eval (exp, env0)))
		|Bval x -> Bval x
		|Fval ((ide1:ide),(exp1:exp)) -> Fval (ide1,exp1)

	(*TBool Operation*)
		|And((exp0:exp),(exp1:exp)) -> (match (eval (exp0,env), eval (exp1,env)) with
			|(Bval(Tbool true),Bval(Tbool true)) -> Bval(Tbool true)
			|(Bval(Tbool _),Bval(Tbool false)) -> Bval(Tbool false)
			|( Bval(Tbool false), Bval(Tbool _)) -> Bval(Tbool false)
			|(_,_) -> raise TypeError)
		|Or((exp0:exp),(exp1:exp)) -> (match (eval (exp0,env), eval (exp1,env)) with
			(Bval(Tbool _),Bval(Tbool true)) -> Bval(Tbool true)
			|( Bval(Tbool true), Bval(Tbool _)) -> Bval(Tbool true)
			|( Bval(Tbool false), Bval(Tbool false)) -> Bval(Tbool false)
			|(_,_) -> raise TypeError)
		|Not((exp0:exp)) -> (match (eval (exp0,env)) with
			|(Bval(Tbool true))-> Bval(Tbool false)
			|( Bval(Tbool false))-> Bval(Tbool true)
			|(_) -> raise TypeError)

	(*Tint TBool*)
		|Sum((exp0:exp),(exp1:exp)) -> (match (eval (exp0,env), eval (exp1,env)) with
			|(Bval(Tint e1), Bval(Tint e2)) -> Bval(Tint( e1 + e2))
			|(_,_)-> raise TypeError)

		|Diff((exp0:exp),(exp1:exp)) -> (match (eval (exp0,env), eval (exp1,env)) with
			|(Bval(Tint e1), Bval(Tint e2)) -> Bval(Tint( e1 - e2))
			|(_,_)-> raise TypeError)

		|Mul((exp0:exp),(exp1:exp)) -> (match (eval (exp0,env), eval (exp1,env)) with
			|(Bval(Tint e1), Bval(Tint e2)) -> Bval(Tint( e1 * e2))
			|(_,_)-> raise TypeError)

		|Mod((exp0:exp)) -> (match (eval(exp0,env)) with
			|(Bval(Tint e1)) -> if e1 < 0 then Bval(Tint (-e1)) else Bval(Tint e1)
			|_ -> raise TypeError)

		|Div((exp0:exp),(exp1:exp)) -> (match (eval (exp0,env), eval (exp1,env)) with
			|(Bval(Tint e1), Bval(Tint e2)) -> Bval(Tint( e1 / e2))
			|(_,_)-> raise TypeError)

	(*Utilities Ops*)
		(*Classic IfThenElse*)
		|Ifthenelse((exp0:exp),(exp1:exp),(exp2:exp)) -> (match (eval(exp0, env)) with
			|Bval(Tbool true) -> (eval(exp1,env))
			|Bval(Tbool false) -> (eval(exp2,env))
			| _ -> raise TypeError)

		(*Check Tuple is empty or not*)
		|IsEmpty((tuple:tuple)) -> (match tuple with
			|() -> Bval(Tbool true)
			| _ -> Bval(Tbool false))

		(*Check if and item belong to the tuple*)
		|In((exp0:exp), (tuple:tuple)) -> (let rec check ((telem: bval list), (k: bval)) = match telem with
					|[] -> Bval(Tbool false)
					|t::ts -> if k = t then Bval(Tbool true) else check (ts, k)
				in
				(let x = (eval(exp0,env))
					in
						(match x with
							|Bval(_) -> (match tuple with
								|() -> failwith "EmptyEnvironment"
								|Add(y) -> check (y, evalBval x) )
							|_ -> raise TypeError)))

		(*Access to i-item*)
		|Access((tuple:tuple),(exp0:exp)) -> (let rec len (list, k, count) = match list with
				|[] -> raise OutOfBound
				|m::ms -> if ((count = k) || (count = eval(Mul(k,Bval(Tint (-1))),env))) then (let sign = eval(Mul(k,Bval(Tint (-1))),env) in (match m with
					|Tbool y -> if sign > Bval(Tint 0) then eval(Not(Bval(Tbool y)),env) else Bval(Tbool y)
					|Tint y -> if sign > Bval(Tint 0) then Bval(Tint (-y)) else Bval(Tint y)
					|Tuple y -> if sign > Bval(Tint 0) then eval(For("x",y,eval(Access(y,exp0),env)) ,env) else Bval(Tuple y)))
				else len(ms,k, eval(Sum(count, Bval(Tint 1)) ,env))
				in
					(let x = (eval(exp0,env)) in (match tuple with
						|() -> failwith "EmptyTuple"
						|Add(y) -> len(y,x,Bval(Tint 0))) ))


		(*Extract a subtuple from a tuple*)
		|Slice((tuple:tuple),(exp0:exp),(exp1:exp)) -> (let rec sliced (inizio,fine,counter) =
			if (counter = inizio || counter =  eval(Mul(inizio,Bval(Tint (-1))),env))
				then (evalBval(eval(Access(tuple,inizio),env)))::(sliced(inizio, fine,eval(Sum(counter,Bval(Tint 1)),env)))
			else if (counter = fine || counter = eval(Mul(fine,Bval(Tint (-1))),env))
				then (evalBval(eval(Access(tuple,fine),env)))::[]
			else (evalBval(eval(Access(tuple,counter),env)))::(sliced(inizio,fine,eval(Sum(counter,Bval(Tint 1)),env)))
				in
					(let a = eval(Mod(exp0),env) in (let b = eval(exp0,env) in (let c = eval(exp1,env) in (match tuple with
						|() -> failwith "EmptyTuple"
						|Add(y) -> if (eval(Mod(b),env) <> eval(Mod(c),env)) then Bval(Tuple(Add(sliced(b,c, a) ) ) ) else raise InvalidOperand)))))

		|LetIn((x:ide),(exp0:exp),(exp1:exp)) -> eval(exp1,(x,exp0)::env)

		(*Apply fun*)
		|For((ide0:ide),(tuple:tuple),(exp1:exp)) -> (if typecheck(exp1) <> Ide "fval"
			then (let rec foride(list) = match list with
				|[] -> []
				|x::xs -> if (typecheck(exp1) = typecheck(Bval(x))) then (evalBval(eval(LetIn(ide0,Bval(x),exp1),env)))::(foride(xs)) else foride(xs)
				in
					(match tuple with
					|() -> failwith "EmptyTuple"
					|Add(y) -> Bval(Tuple(Add(  foride(y) ) ) ) ) )
			else raise TypeError)


		|Appl((name:ide),(value:exp)) -> (let rec findFun list = match list with
				|(id,param,body,attEnv)::xs -> if id = name then eval(LetIn(param,eval(value,attEnv),body),attEnv)
											else findFun xs
				|[] -> failwith("Unbound function name")
			in findFun !funenv);;


(*---------------------TESTING---------------------*)

bind("x",Bval(Tint 3));;
let fv = Fval("y",Sum(Ide "x",Bval(Tint 5)));;
decFun "somma" fv;;
let ap1 = Appl("ciao", Bval(Tint 3));;
let ap2 = Appl("somm", Bval(Tint 3));;
eval(ap1,!env);;
eval(ap2,!env);;


bind("a",Bval(Tint 4));;
bind("b",Bval(Tbool false));;
eval(And(Ide "b",Bval(Tbool true)),!env);;
eval(And(Ide "a",Bval(Tbool true)),!env);;
eval(Or(Ide "b",Bval(Tbool true)),!env);;
eval(Not(Ide "b"),!env);;
eval(Sum(Ide "a",Bval(Tint 3)),!env);;

eval(Ifthenelse(And(Bval(Tbool true),Bval(Tbool false)), Diff(Ide "a",Bval(Tint 2)), Mul(Ide "a",Bval(Tint 2))),!env);;
bind("t",Bval(Tuple(())));;
eval(IsEmpty(evalToTuple(evalBval(eval(Ide "t",!env)))),!env);;

bind("t",Bval(Tuple(Add(Tint 4::Tbool false::Tint 5::Tbool true::[]))));;
eval(IsEmpty(evalToTuple(evalBval(eval(Ide "t",!env)))),!env);;

let t = Add(Tint 4::Tbool false:: Tbool true:: Tint 6::Tuple(Add(Tint 6::Tbool true::[]))::[]);;
let a1 = Access(t,Bval(Tint (-1)));;
let a2 = Access(t,Bval(Tint (3)));;
let a3 = Access(t,Bval(Tint 4));;
let a4 = Access(t,Bval(Tint 5));;
let a5 = Access(t,Bval(Tbool true));;
eval(a1,!env);;
eval(a2,!env);;
eval(a3,!env);;
eval(a4,!env);;
eval(a5,!env);;

let sl1 = Slice(t,Bval(Tint (-1)), Bval(Tint 3));;
let sl2 = Slice(t,Bval(Tint 3),Bval(Tint 7));;
eval(sl1,!env);;
eval(sl2,!env);;

let in1 = In(Bval(Tint 4),t);;
let in2 = In(Bval(Tint 10),t);;
eval(in1,!env);;
eval(in2,!env);;


let let1 = LetIn("x",Bval(Tint 4), Sum(Ide"x", Bval(Tint 3)));;
eval(let1, !env);;

let fr = For("x", Add(Tint 4::Tint 3::Tbool false::[]), Sum(Ide "x",Bval(Tint 29)));;
eval(fr, !env);;

let fr1 = For("x", Add(Tbool true::Tint 4::Tint 3::Tbool false::[]), Not(Ide "x"));;
eval(fr1, !env);;


(*---------------------END---------------------*)
