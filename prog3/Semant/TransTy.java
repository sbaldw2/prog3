package Semant;
import Translate.Exp;
import Types.Type;

public class TransTy extends Trans {

	public TransTy(Env e) {
		env = e;
	}

	public Type transTy(Absyn.Ty t) {
		if (t instanceof Absyn.ArrayTy)
			return transTy((Absyn.ArrayTy)t);
		else if (t instanceof Absyn.NameTy)
			return transTy((Absyn.NameTy)t);
		else if (t instanceof Absyn.RecordTy)
			return transTy((Absyn.RecordTy)t);
		else throw new Error("TransTy.transTy");
	}

	/* TODO: Implement the below stubbed methods */

	public Type transTy(Absyn.ArrayTy t) {
		Types.NAME type = (Types.NAME)env.tenv.get(t.typ);
		return new Types.ARRAY(type);
	}

	public Type transTy(Absyn.NameTy t) {
		Types.NAME type = (Types.NAME)env.tenv.get(t.name);
		return type;
	}

	public Type transTy(Absyn.RecordTy t) {
		return new Types.NIL();
	}

}
