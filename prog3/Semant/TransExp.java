package Semant;
import Translate.Exp;
import Types.Type;

public class TransExp extends Trans {
	TransVar transVarObj = new TransVar(env);

	public TransExp(Env e) {
		env = e;
	}

	public ExpTy transExp(Absyn.Exp e) {
		ExpTy result;

		if (e == null)
			return new ExpTy(null, VOID);
		else if (e instanceof Absyn.OpExp)
			result = transExp((Absyn.OpExp)e);
		else if (e instanceof Absyn.LetExp)
			result = transExp((Absyn.LetExp)e);
		else if (e instanceof Absyn.IntExp)
			result = transExp((Absyn.IntExp)e);
		else if (e instanceof Absyn.StringExp)
			result = transExp((Absyn.StringExp)e);
		else if (e instanceof Absyn.SeqExp)
			result = transExp((Absyn.SeqExp)e);
		else if (e instanceof Absyn.ArrayExp)
			result = transExp((Absyn.ArrayExp)e);
		else if (e instanceof Absyn.NilExp)
			result = transExp((Absyn.NilExp)e);
		else if (e instanceof Absyn.RecordExp)
			result = transExp((Absyn.RecordExp)e);
		else if (e instanceof Absyn.AssignExp)
			result = transExp((Absyn.AssignExp)e);
		else if (e instanceof Absyn.BreakExp)
			result = transExp((Absyn.BreakExp)e);
		else if (e instanceof Absyn.CallExp)
			result = transExp((Absyn.CallExp)e);
		else if (e instanceof Absyn.ForExp)
			result = transExp((Absyn.ForExp)e);
		else if (e instanceof Absyn.WhileExp)
			result = transExp((Absyn.WhileExp)e);
		else if (e instanceof Absyn.IfExp)
			result = transExp((Absyn.IfExp)e);
		else
			throw new Error("TransExp.transExp");

		e.type = result.ty;
		return result;
	}

	/*
	 * TransExp Overrides
	 */

	public ExpTy transExp(Absyn.OpExp e) {
		ExpTy left = transExp(e.left);
		ExpTy right = transExp(e.right);

		switch (e.oper) {
			case Absyn.OpExp.PLUS:
			case Absyn.OpExp.MINUS:
			case Absyn.OpExp.MUL:
			case Absyn.OpExp.DIV:
				checkInt(left, e.left.pos);
				checkInt(right, e.right.pos);
				return new ExpTy(null, INT);
			case Absyn.OpExp.EQ:
			case Absyn.OpExp.NE:
				checkComparable(left, e.left.pos);
				checkComparable(right, e.right.pos);
				return new ExpTy(null, INT);
			case Absyn.OpExp.LT:
			case Absyn.OpExp.GT:
			case Absyn.OpExp.LE:
			case Absyn.OpExp.GE:
				checkOrderable(left, e.left.pos);
				checkOrderable(right, e.right.pos);
				return new ExpTy(null, INT);
			default:
				throw new Error("unknown operator");
		}
	}

	public ExpTy transExp(Absyn.ArrayExp e) {
		Types.NAME type = (Types.NAME)env.tenv.get(e.typ);

		ExpTy size = transExp(e.size);
		ExpTy init = transExp(e.init);

		checkInt(size, e.size.pos);

		if (type == null) {
			error(e.pos, "array of type " + e.typ + " undefined");
			return new ExpTy(null, VOID);
		} else if (!(type.actual() instanceof Types.ARRAY)) {
			error(e.pos, "not an array type");
			return new ExpTy(null, VOID);
		}

		Type element = ((Types.ARRAY)type.actual()).element;

		if (!init.ty.coerceTo(element))
			error(e.init.pos, "initial element does not match array's type");

		return new ExpTy(null, type);
	}

	public ExpTy transExp(Absyn.AssignExp e) {
		ExpTy varTy = transVarObj.transVar(e.var);
		ExpTy expTy = transVarObj.transExp(e.exp);

		if (!varTy.ty.coerceTo(expTy.ty))
			error(e.pos, "assigment types do not match");

		return new ExpTy(null, VOID);
	}

	public ExpTy transExp(Absyn.BreakExp e) {
		return new ExpTy(null, VOID);
	}

	public ExpTy transExp(Absyn.CallExp e) {
		Entry entry = (Entry)env.venv.get(e.func);

		if (entry == null | !(entry instanceof FunEntry)) {
			error(e.pos, "undefinded function: " + e.func);
			return new ExpTy(null, VOID);
		}

		FunEntry funEntry = (FunEntry)entry;
		Absyn.ExpList argument = e.args;
		Types.RECORD record = funEntry.formals;
		
		while (argument != null) {
			ExpTy argumentTy = transExp(argument.head);
			if (record == null) 
				error(argument.head.pos, "too many arguments");
			else if (!argumentTy.ty.coerceTo(record.fieldType))
				error(argument.head.pos, "argument is of wrong type");

			argument = argument.tail;
			record = record.tail;
		}

		if (record != null)
			error(e.pos, "Not enough arguments");

		return new ExpTy(null, funEntry.result);
	}

	public ExpTy transExp(Absyn.ForExp e) {
		ExpTy loExpTy = transExp(e.var.init);
		ExpTy hiExpTy = transExp(e.hi);

		if (!(loExpTy.ty.coerceTo(INT) && hiExpTy.ty.coerceTo(INT)))
			error(e.pos, "for loop parameters should be of type int");

		env.venv.beginScope();

		transDec(e.var);
		ExpTy bodyExpTy = transExp(e.body);

		if (!bodyExpTy.ty.coerceTo(VOID))
			error(e.pos, "body of wa while loop should not have a value");

		env.venv.endScope();

		return new ExpTy(null, VOID);
	}

	public ExpTy transExp(Absyn.WhileExp e) {
		ExpTy testType = transExp(e.test);
		ExpTy bodyType = transExp(e.body);

		if (!testType.ty.coerceTo(INT))
			error(e.test.pos, "test should be an integer");

		if (!bodyType.ty.coerceTo(VOID))
			error(e.body.pos, "a while loop should not be value");

		return new ExpTy(null, VOID);
	}

	public ExpTy transExp(Absyn.IfExp e) {
		ExpTy test = transExp(e.test);
		checkInt(test, e.test.pos);

		ExpTy thenClause = transExp(e.thenclause);

		if (e.elseclause != null) {
			ExpTy elseClause = transExp(e.elseclause);
			if (!thenClause.ty.coerceTo(elseClause.ty))
				error(e.pos, "if statement then/else does not match");
			return thenClause;
		}
		return thenClause;
	}

	public ExpTy transExp(Absyn.IntExp e) {
		return new ExpTy(null, INT);
	}

	public ExpTy transExp(Absyn.LetExp e) {
		env.venv.beginScope();
		env.tenv.beginScope();

		for (Absyn.DecList d = e.decs; d != null; d = d.tail)
			transDec(d.head);

		ExpTy body = transExp(e.body);
		env.venv.endScope();
		env.tenv.endScope();


		return new ExpTy(null, body.ty);
	}

	public ExpTy transExp(Absyn.NilExp e) {
		return new ExpTy(null, NIL);
	}

	public ExpTy transExp(Absyn.RecordExp e) {
		Types.NAME type = (Types.NAME)env.tenv.get(e.typ);

		if (type == null || !(type.actual() instanceof Types.RECORD)) {
			error(e.pos, "Record type undefined: " + e.typ);
			return new ExpTy(null, VOID);
		}

		Types.RECORD record = (Types.RECORD)type.actual();

		for (Absyn.FieldExpList field = e.fields; field != null; field = field.tail) {
			ExpTy value = transExp(field.init);

			if (record == null)
				error(e.pos, "too many arguments for record type: " + e.typ);
			else if (field.name != record.fieldName)
				error(e.pos, "field names are not aligned");
			else if (!value.ty.coerceTo(record.fieldType))
				error(e.pos, "field types do not match");

			if (record != null) 
				record = record.tail;
		}
		
		if (record != null)
			error(e.pos, "not enough arguments for record type: " + e.typ);

		return new ExpTy(null, type);
	}

	public ExpTy transExp(Absyn.SeqExp e) {
		ExpTy expTy = transExp(e.list.head);

		if (e.list.tail == null)
			return expTy;
		else
			return transExp(new Absyn.SeqExp(e.list.tail.head.pos, e.list.tail));
	}

	public ExpTy transExp(Absyn.StringExp e) {
		return new ExpTy(null, STRING);
	}

	public ExpTy transExp(Absyn.VarExp e) {
		return transVarObj.transVar(e.var);
	}

}
