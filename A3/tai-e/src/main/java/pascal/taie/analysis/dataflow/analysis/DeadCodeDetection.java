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

package pascal.taie.analysis.dataflow.analysis;

import pascal.taie.analysis.MethodAnalysis;
import pascal.taie.analysis.dataflow.analysis.constprop.CPFact;
import pascal.taie.analysis.dataflow.analysis.constprop.ConstantPropagation;
import pascal.taie.analysis.dataflow.analysis.constprop.Value;
import pascal.taie.analysis.dataflow.fact.DataflowResult;
import pascal.taie.analysis.dataflow.fact.SetFact;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.analysis.graph.cfg.CFGBuilder;
import pascal.taie.analysis.graph.cfg.Edge;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.stmt.AssignStmt;
import pascal.taie.ir.stmt.If;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.ir.stmt.SwitchStmt;
import pascal.taie.util.collection.Pair;

import java.util.*;

public class DeadCodeDetection extends MethodAnalysis {

    public static final String ID = "deadcode";

    public DeadCodeDetection(AnalysisConfig config) {
        super(config);
    }

    @Override
    public Set<Stmt> analyze(IR ir) {
        // obtain CFG
        CFG<Stmt> cfg = ir.getResult(CFGBuilder.ID);
        // obtain result of constant propagation
        DataflowResult<Stmt, CPFact> constants = ir.getResult(ConstantPropagation.ID);
        // obtain result of live variable analysis
        DataflowResult<Stmt, SetFact<Var>> liveVars = ir.getResult(LiveVariableAnalysis.ID);
        // keep statements (dead code) sorted in the resulting set
        Set<Stmt> deadCode = new TreeSet<>(Comparator.comparing(Stmt::getIndex));
        // TODO - finish me
        // Your task is to recognize dead code in ir and add it to deadCode

        Set<Stmt> livecode = new TreeSet<>(Comparator.comparing(Stmt::getIndex));
        Queue<Stmt> stmt_queue = new LinkedList<>();

        stmt_queue.add(cfg.getEntry()); // 要遍历的所有语句
        while (!stmt_queue.isEmpty()) {
            Stmt stmt = stmt_queue.poll();

            /* dead assignment */
            if (stmt instanceof AssignStmt<?,?> assign_stmt && assign_stmt.getLValue() instanceof Var var) {
                SetFact<Var> live_variable_analysis_result = liveVars.getOutFact(stmt); // 活跃变量分析结果
                if (!live_variable_analysis_result.contains(var) &&
                        hasNoSideEffect(assign_stmt.getRValue())) { // 无用变量 且 无副作用 -> deadcode
                    // "标记"deadcode, 分析所有后继
                    stmt_queue.addAll(cfg.getSuccsOf(stmt));
                    continue;
                }
            }

            // 把该stmt标为livecode(走到这里的都是livecode), 因此后面的分析都只寻找livecode!!
            if (!livecode.add(stmt)) { // 如果已经存在(分析过), 下一轮
                continue;
            }

            /* unreachable code: unreachable branch */
            if (stmt instanceof If if_stmt) { // if语句
                CPFact constant_propagation_result = constants.getInFact(stmt); // 常量传播结果
                Value condition = ConstantPropagation.evaluate(if_stmt.getCondition(), constant_propagation_result);
                if (condition.isConstant()) {
                    Set<Edge<Stmt>> out_edges= cfg.getOutEdgesOf(if_stmt); // 出边
                    for (Edge<Stmt> out_edge : out_edges) {
                        if (condition.getConstant() == 1 && out_edge.getKind() == Edge.Kind.IF_TRUE ||      // 条件永真
                                condition.getConstant() == 0 && out_edge.getKind() == Edge.Kind.IF_FALSE) { // 条件永假
                            // 永真的分支 -> livecode
                            stmt_queue.add(out_edge.getTarget());
                            break; // break for
                        }
                    }
                } else { // 普通的if语句, 分析所有后继
                    stmt_queue.addAll(cfg.getSuccsOf(stmt));
                }
            } else if (stmt instanceof SwitchStmt switch_stmt) { // switch语句
                CPFact constant_propagation_result = constants.getInFact(stmt); // 常量传播结果
                Value value = constant_propagation_result.get(switch_stmt.getVar());

                if (value.isConstant()) {
                    boolean flag = false;
                    for (Pair<Integer, Stmt> pair : switch_stmt.getCaseTargets()) {
                        if(pair.first() == value.getConstant()){
                            flag = true;
                            stmt_queue.add(pair.second()); // 永真case -> livecode
                        }
                    }
                    if (!flag) { // 没有其他case是永真, default case就是永真
                        stmt_queue.add(((SwitchStmt) stmt).getDefaultTarget());
                    }
                } else { // 普通的switch语句, 分析所有后继
                    stmt_queue.addAll(cfg.getSuccsOf(stmt));
                }
            } else { // 普通的语句, 分析所有后继
                stmt_queue.addAll(cfg.getSuccsOf(stmt));
            }
        }

        deadCode.addAll(cfg.getNodes());
        deadCode.removeAll(livecode);
        deadCode.remove(cfg.getExit());

        return deadCode;
    }

    /**
     * @return true if given RValue has no side effect, otherwise false.
     */
    private static boolean hasNoSideEffect(RValue rvalue) {
        // new expression modifies the heap
        if (rvalue instanceof NewExp ||
                // cast may trigger ClassCastException
                rvalue instanceof CastExp ||
                // static field access may trigger class initialization
                // instance field access may trigger NPE
                rvalue instanceof FieldAccess ||
                // array access may trigger NPE
                rvalue instanceof ArrayAccess) {
            return false;
        }
        if (rvalue instanceof ArithmeticExp) {
            ArithmeticExp.Op op = ((ArithmeticExp) rvalue).getOperator();
            // may trigger DivideByZeroException
            return op != ArithmeticExp.Op.DIV && op != ArithmeticExp.Op.REM;
        }
        return true;
    }
}
