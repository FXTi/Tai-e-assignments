/*
 * Tai-e: A Static Analysis Framework for Java
 *
 * Copyright (C) 2022 Tian Tan <tiantan@nju.edu.cn>
 * Copyright (C) 2022 Yue Li <yueli@nju.edu.cn>
 *
 * This file is part of Tai-e.
 *
 * Tai-e is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License
 * as published by the Free Software Foundation, either version 3
 * of the License, or (at your option) any later version.
 *
 * Tai-e is distributed in the hope that it will be useful,but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
 * or FITNESS FOR A PARTICULAR PURPOSE. See the GNU Lesser General
 * Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with Tai-e. If not, see <https://www.gnu.org/licenses/>.
 */

package pascal.taie.analysis.dataflow.analysis.constprop;

import pascal.taie.analysis.dataflow.analysis.AbstractDataflowAnalysis;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.ArithmeticExp;
import pascal.taie.ir.exp.BinaryExp;
import pascal.taie.ir.exp.BitwiseExp;
import pascal.taie.ir.exp.ConditionExp;
import pascal.taie.ir.exp.Exp;
import pascal.taie.ir.exp.IntLiteral;
import pascal.taie.ir.exp.ShiftExp;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.AssignStmt;
import pascal.taie.ir.stmt.DefinitionStmt;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.language.type.PrimitiveType;
import pascal.taie.language.type.Type;
import pascal.taie.util.AnalysisException;

public class ConstantPropagation extends
        AbstractDataflowAnalysis<Stmt, CPFact> {

    public static final String ID = "constprop";

    public ConstantPropagation(AnalysisConfig config) {
        super(config);
    }

    @Override
    public boolean isForward() {
        return true;
    }

    @Override
    public CPFact newBoundaryFact(CFG<Stmt> cfg) {
        return new CPFact();
    }

    @Override
    public CPFact newInitialFact() {
        return new CPFact();
    }

    @Override
    public void meetInto(CPFact fact, CPFact target) {
        fact.entries().forEach(entry -> target.update(entry.getKey(), meetValue(target.get(entry.getKey()), entry.getValue())));
    }

    /**
     * Meets two Values.
     */
    public Value meetValue(Value v1, Value v2) {
        if (v1.isNAC() || v2.isNAC()) {
            return Value.getNAC();
        }
        if (v1.isConstant() && v2.isConstant()) {
            return v1.equals(v2) ? v1 : Value.getNAC();
        }
        return v1.isUndef() ? v2 : v1;
    }

    @Override
    public boolean transferNode(Stmt stmt, CPFact in, CPFact out) {
        CPFact newOut = in.copy();

        if (stmt instanceof DefinitionStmt
                && stmt.getDef().filter(v -> v instanceof Var && canHoldInt((Var) v)).isPresent()) {
            newOut.update((Var) ((DefinitionStmt) stmt).getLValue(), evaluate(((DefinitionStmt) stmt).getRValue(), in));
        }

        boolean result = !newOut.equals(out);
        out.clear();
        out.copyFrom(newOut);

        return result;
    }

    /**
     * @return true if the given variable can hold integer value, otherwise false.
     */
    public static boolean canHoldInt(Var var) {
        Type type = var.getType();
        if (type instanceof PrimitiveType) {
            switch ((PrimitiveType) type) {
                case BYTE:
                case SHORT:
                case INT:
                case CHAR:
                case BOOLEAN:
                    return true;
            }
        }
        return false;
    }

    /**
     * Evaluates the {@link Value} of given expression.
     *
     * @param exp the expression to be evaluated
     * @param in  IN fact of the statement
     * @return the resulting {@link Value}
     */
    public static Value evaluate(Exp exp, CPFact in) {
        if (exp instanceof IntLiteral) {
            return Value.makeConstant(((IntLiteral) exp).getValue());
        }
        if (exp instanceof Var) {
            return in.get((Var) exp);
        }
        if (exp instanceof ArithmeticExp) {
            final Value right = evaluate(((ArithmeticExp) exp).getOperand2(), in);
            if (right.isConstant() && right.getConstant() == 0
                    && (((ArithmeticExp) exp).getOperator() == ArithmeticExp.Op.DIV
                        || ((ArithmeticExp) exp).getOperator() == ArithmeticExp.Op.REM)) {
                return Value.getUndef();
            }
        }
        if (exp instanceof BinaryExp) {
            final BinaryExp binaryExp = (BinaryExp) exp;
            final Value left = evaluate(binaryExp.getOperand1(), in);
            final Value right = evaluate(binaryExp.getOperand2(), in);

            if (left.isNAC() || right.isNAC()) {
                return Value.getNAC();
            }
            if (!left.isConstant() || !right.isConstant()) {
                return Value.getUndef();
            }

            if (binaryExp instanceof ArithmeticExp) {
                final ArithmeticExp arithmeticExp = (ArithmeticExp) binaryExp;
                switch (arithmeticExp.getOperator()) {
                    case ADD: return Value.makeConstant(left.getConstant() + right.getConstant());
                    case SUB: return Value.makeConstant(left.getConstant() - right.getConstant());
                    case MUL: return Value.makeConstant(left.getConstant() * right.getConstant());
                    case DIV: return right.getConstant() == 0
                                ? Value.getUndef()
                                : Value.makeConstant(left.getConstant() / right.getConstant());
                    case REM: return right.getConstant() == 0
                                ? Value.getUndef()
                                : Value.makeConstant(left.getConstant() % right.getConstant());
                }
            }
            if (binaryExp instanceof ConditionExp) {
                final ConditionExp conditionExp = (ConditionExp) binaryExp;
                switch (conditionExp.getOperator()) {
                    case EQ: return Value.makeConstant(left.getConstant() == right.getConstant() ? 1 : 0);
                    case NE: return Value.makeConstant(left.getConstant() != right.getConstant() ? 1 : 0);
                    case LT: return Value.makeConstant(left.getConstant() < right.getConstant() ? 1 : 0);
                    case GT: return Value.makeConstant(left.getConstant() > right.getConstant() ? 1 : 0);
                    case LE: return Value.makeConstant(left.getConstant() <= right.getConstant() ? 1 : 0);
                    case GE: return Value.makeConstant(left.getConstant() >= right.getConstant() ? 1 : 0);
                }
            }
            if (binaryExp instanceof ShiftExp) {
                final ShiftExp shiftExp = (ShiftExp) binaryExp;
                switch (shiftExp.getOperator()) {
                    case SHL: return Value.makeConstant(left.getConstant() << right.getConstant());
                    case SHR: return Value.makeConstant(left.getConstant() >> right.getConstant());
                    case USHR: return Value.makeConstant(left.getConstant() >>> right.getConstant());
                }
            }
            if (binaryExp instanceof BitwiseExp) {
                final BitwiseExp bitwiseExp = (BitwiseExp) binaryExp;
                switch (bitwiseExp.getOperator()) {
                    case OR: return Value.makeConstant(left.getConstant() | right.getConstant());
                    case AND: return Value.makeConstant(left.getConstant() & right.getConstant());
                    case XOR: return Value.makeConstant(left.getConstant() ^ right.getConstant());
                }
            }
        }
        return Value.getNAC();
    }
}
