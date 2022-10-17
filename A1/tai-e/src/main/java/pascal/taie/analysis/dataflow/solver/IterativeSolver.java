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

package pascal.taie.analysis.dataflow.solver;

import pascal.taie.analysis.dataflow.analysis.DataflowAnalysis;
import pascal.taie.analysis.dataflow.fact.DataflowResult;
import pascal.taie.analysis.graph.cfg.CFG;

class IterativeSolver<Node, Fact> extends Solver<Node, Fact> {

    public IterativeSolver(DataflowAnalysis<Node, Fact> analysis) {
        super(analysis);
    }

    @Override
    protected void doSolveForward(CFG<Node> cfg, DataflowResult<Node, Fact> result) {
        throw new UnsupportedOperationException();
    }

    @Override
    protected void doSolveBackward(CFG<Node> cfg, DataflowResult<Node, Fact> result) {
        // TODO - finish me
        boolean flag = true;
        while (flag) {
            flag = false;
            for (Node node : cfg) {
                if (!cfg.isExit(node)) {
                    Fact out_fact = analysis.newInitialFact(); // 创建临时outFact, 最后覆盖目标outFact
                    for (Node succ : cfg.getSuccsOf(node)) { // 取出B的所有后继
                        analysis.meetInto(result.getInFact(succ), out_fact); // in_fact并集赋给out_fact, 注意out_fact一开始是空集！
                    }
                    result.setOutFact(node, out_fact); // 覆盖
                    if (analysis.transferNode(node, result.getInFact(node), result.getOutFact(node))) {
                        flag = true; // 一旦变了, 循环继续
                    }
                }
            }
        }
    }
}
