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
import pascal.taie.ir.exp.*;
import pascal.taie.ir.stmt.DefinitionStmt;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.language.type.PrimitiveType;
import pascal.taie.language.type.Type;
import pascal.taie.util.AnalysisException;

import java.util.List;

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
        // TODO - finish me
        List<Var> var_list =  cfg.getIR().getParams();
        CPFact cpFact = new CPFact();
        var_list.forEach(var -> {
            if (canHoldInt(var)) { // 将每个会被分析的方法的参数的值初始化为 NAC
                cpFact.update(var, Value.getNAC());
            }
        });
        return cpFact;
    }

    @Override
    public CPFact newInitialFact() {
        // TODO - finish me
        return new CPFact();
    }

    @Override
    public void meetInto(CPFact fact, CPFact target) {
        // TODO - finish me
        fact.forEach((key, value) -> {
            target.update(key, meetValue(value, target.get(key)));
        });
    }

    /**
     * Meets two Values.
     */
    public Value meetValue(Value v1, Value v2) {
        // TODO - finish me
        if(v1.isNAC() || v2.isNAC()) {
            return Value.getNAC();
        } else if (v1.isUndef()) {
            return v2;
        } else if (v2.isUndef()) {
            return v1;
        } else {
            return v1.equals(v2) ? v1 : Value.getNAC();
        }
    }

    @Override
    public boolean transferNode(Stmt stmt, CPFact in, CPFact out) {
        // TODO - finish me
        if (stmt instanceof DefinitionStmt<?,?> definitionStmt) {
            LValue lValue = definitionStmt.getLValue();
            if (lValue instanceof Var lVar) { // 需要判断!!
                final boolean[] flag = {false};
                CPFact in_copy = in.copy();
                in_copy.remove(lVar); // kill
                in_copy.forEach((key, value) -> {
                    if (out.update(key, value)) {
                        flag[0] = true;
                    }
                });

                if (canHoldInt(lVar) && out.update(lVar, evaluate(definitionStmt.getRValue(), in))) {
                    flag[0] = true;
                }
                return flag[0];
            }
        }
        return out.copyFrom(in);
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
        // TODO - finish me
        if (exp instanceof Var var) { // 变量
            return canHoldInt(var) ? in.get(var) : Value.getNAC();
        } else if (exp instanceof IntLiteral intLiteral) { // 字面量
            return Value.makeConstant(intLiteral.getValue());
        } else if (exp instanceof BinaryExp binaryExp) { // 二元运算
            Value operand1 = evaluate(binaryExp.getOperand1(), in);
            Value operand2 = evaluate(binaryExp.getOperand2(), in);
            if ((binaryExp.getOperator() == ArithmeticExp.Op.DIV || binaryExp.getOperator() == ArithmeticExp.Op.REM)
                    && operand2.isConstant() && operand2.getConstant() == 0) {
                return Value.getUndef(); // 只要后者为0, 前面不管是什么都是undef
            } else if (operand1.isNAC() || operand2.isNAC()) {
                return Value.getNAC();
            } else if (operand1.isConstant() && operand2.isConstant()) {
                return binary_operation(binaryExp.getOperator(), operand1.getConstant(), operand2.getConstant());
            } else {
                return Value.getUndef();
            }
        }
        return Value.getNAC();
    }

    public static Value binary_operation(BinaryExp.Op operator, int operand1, int operand2) {
        int result = 0;
        if (operator instanceof ArithmeticExp.Op arithmeticOp) {
            result = switch (arithmeticOp) {
                case ADD -> operand1 + operand2;
                case SUB -> operand1 - operand2;
                case MUL -> operand1 * operand2;
                case DIV -> operand1 / operand2;
                case REM -> operand1 % operand2;
            };
        } else if (operator instanceof ConditionExp.Op conditionOp) {
            result = switch (conditionOp) {
                case EQ -> (operand1 == operand2) ? 1 : 0;
                case GE -> (operand1 >= operand2) ? 1 : 0;
                case GT -> (operand1 > operand2) ? 1 : 0;
                case LE -> (operand1 <= operand2) ? 1 : 0;
                case LT -> (operand1 < operand2) ? 1 : 0;
                case NE -> (operand1 != operand2) ? 1 : 0;
            };
        } else if (operator instanceof ShiftExp.Op shiftOp) {
            result = switch (shiftOp) {
                case SHL -> operand1 << operand2;
                case SHR -> operand1 >> operand2;
                case USHR -> operand1 >>> operand2;
            };
        } else if (operator instanceof BitwiseExp.Op bitwiseOp) {
            result = switch (bitwiseOp) {
                case OR -> operand1 | operand2;
                case AND -> operand1 & operand2;
                case XOR -> operand1 ^ operand2;
            };
        } else {
            throw new AnalysisException("No such Operator: " + operator);
        }
        return Value.makeConstant(result);
    }
}
