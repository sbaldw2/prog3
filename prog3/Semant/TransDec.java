package Semant;
import Translate.Exp;
import Types.Type;

public class TransDec extends Trans {

	public TransDec(Env e) {
		env = e;
	}

	TransTy transTyObj = new TransTy(env);

	public void transDec(Absyn.Dec d) {
		if (d instanceof Absyn.FunctionDec)
			transDec((Absyn.FunctionDec)d);
		else if (d instanceof Absyn.VarDec)
			transDec((Absyn.VarDec)d);
		else if (d instanceof Absyn.TypeDec)
			transDec((Absyn.TypeDec)d);
		else
			throw new Error("TransDec.transDec");
	}

	/* TODO: Implement the below stubbed methods */


	public void transDec(Absyn.FunctionDec d) {
		Absyn.FunctionDec func = d;
		while (func != null) {
			// Type-check the fields while creating record type
			Types.RECORD initialField = null;
			Types.RECORD fields = null;
			Absyn.FieldList param = func.params;
			while (param != null) {
				// Lookup the type
				Types.NAME type = (Types.NAME)env.tenv.get(param.typ);

				if (type == null)
					error(param.pos, "type undefined");

				// Add type to record
				if (initialField == null) {
					initialField = new Types.RECORD(param.name, type, null);
					fields = initialField;
				}
				else {
					fields.tail = new Types.RECORD(param.name, type, null);
					fields = fields.tail;
				}

				param = param.tail;
			}

			// Figure out the return type
			Type returnType = VOID;
			if (func.result != null)
				returnType = transTyObj.transTy(func.result);

			// Add function to environment
			func.entry = new FunEntry(initialField, returnType);
			env.venv.put(func.name, func.entry);

			func = func.next;
		}

		// Loop again for the function bodies
		Absyn.FunctionDec fun = d;
		while (fun != null) {
			env.venv.beginScope();
			Types.RECORD parameter;
			for (parameter = fun.entry.formals; parameter != null; parameter = parameter.tail) {
				env.venv.put(parameter.fieldName, new VarEntry(parameter.fieldType));
			}

			// Analyze function body
			ExpTy funcBody = transExp(fun.body);

			if (!funcBody.ty.coerceTo(fun.entry.result))
				error(fun.body.pos, "function return type is incorrect");

			env.venv.endScope();

			fun = fun.next;
		}
	}

	// Translate the value being assigned to the variable
	public void transDec(Absyn.VarDec d) {
		ExpTy init = transExp(d.init);

		// Get the type of the variable
		Type type = null;

		// Use the initial type of the variable if not specified
		if (d.typ == null)
			type = init.ty;

		// If it is specified, translate it and check compatibility
		else {
			type = transTyObj.transTy(d.typ);
			if (!init.ty.coerceTo(type))
				error(d.pos, "types are not compatible");
		}

		// Add variable to the variable environment
		d.entry = new VarEntry(type);
		env.venv.put(d.name, d.entry);
	}

	// Recursively process the type decs
	public void transDec(Absyn.TypeDec d) {
		// Create the NAME object
		Types.NAME name = new Types.NAME(d.name);
		name.bind(transTyObj.transTy(d.ty));
		d.entry = name;

		// Put type dec in the env
		env.tenv.put(d.name, d.entry);

		// Process another type if there is one
		if (d.next != null)
			transDec(d.next);
	}
}
