package Semant;
import Translate.Exp;
import Types.Type;

public class TransVar extends Trans {

	public TransVar(Env e) {
		env = e;
	}

	public ExpTy transVar(Absyn.Var v) {
		if (v instanceof Absyn.FieldVar)
			return transVar((Absyn.FieldVar) v);
		else if (v instanceof Absyn.SimpleVar)
			return transVar((Absyn.SimpleVar) v);
		else if (v instanceof Absyn.SubscriptVar)
			return transVar((Absyn.SubscriptVar) v);
		else
			throw new Error("TransVar.transVar");
	}

	/* TODO: Implement the below stubbed methods */
	
	public ExpTy transVar(Absyn.FieldVar v) {
		return new ExpTy(null, VOID);
	}

	public ExpTy transVar(Absyn.SimpleVar v) {
		return new ExpTy(null, VOID);
	}

	public ExpTy transVar(Absyn.SubscriptVar v) {
		return new ExpTy(null, VOID);
	}
}
