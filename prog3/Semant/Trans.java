package Semant;
import Translate.Exp;
import Types.Type;

public abstract class Trans {
	static final Types.VOID		VOID		= new Types.VOID();
	static final Types.INT		INT			= new Types.INT();
	static final Types.STRING	STRING	= new Types.STRING();
	static final Types.NIL		NIL			= new Types.NIL();

	Env env;

	protected void error(int pos, String msg) {
		env.errorMsg.error(pos, msg);
	}

	public ExpTy transExp(Absyn.Exp e) {
		TransExp transExpObj = new TransExp(env);
		return transExpObj.transExp(e);
	}

	public void transDec(Absyn.Dec d) {
		TransDec transDecObj = new TransDec(env);
		transDecObj.transDec(d);
	}

	public Type transType(Absyn.Ty t) {
		TransTy transTyObj = new TransTy(env);
		return transTyObj.transTy(t);
	}

	public ExpTy transVar(Absyn.Var v) {
		TransVar transVarObj = new TransVar(env);
		return transVarObj.transVar(v);
	}

	protected Exp checkInt(ExpTy et, int pos) {
		if (!INT.coerceTo(et.ty))
			error(pos, "integer required");
		return et.exp;
	}

	protected Exp checkComparable(ExpTy et, int pos) {
		Type type = et.ty.actual();
		if (!(type instanceof Types.INT || type instanceof Types.STRING || type instanceof Types.NIL || type instanceof Types.RECORD || type instanceof Types.ARRAY))
      error(pos, "type is not comparable");
    return et.exp;
	}
	
	protected Exp checkOrderable(ExpTy et, int pos) {
    Type type = et.ty.actual();
    if (!(type instanceof Types.INT || type instanceof Types.STRING))
      error(pos, "integer or string required");
    return et.exp;
  }	

}
