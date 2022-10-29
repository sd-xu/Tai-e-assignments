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

import java.util.LinkedList;

class WorkListSolver<Node, Fact> extends Solver<Node, Fact> {

    WorkListSolver(DataflowAnalysis<Node, Fact> analysis) {
        super(analysis);
    }

    @Override
    protected void doSolveForward(CFG<Node> cfg, DataflowResult<Node, Fact> result) {
        // TODO - finish me
        LinkedList<Node> worklist = new LinkedList<>(cfg.getNodes());
        while (!worklist.isEmpty()) {
            Node node = worklist.pollFirst();
            Fact in_fact = result.getInFact(node);
            for (Node pred : cfg.getPredsOf(node)) {
                analysis.meetInto(result.getOutFact(pred), in_fact);
            }

            if (analysis.transferNode(node, result.getInFact(node), result.getOutFact(node))) {
                worklist.addAll(cfg.getSuccsOf(node));
            }
        }
    }

    @Override
    protected void doSolveBackward(CFG<Node> cfg, DataflowResult<Node, Fact> result) {
        // TODO - finish me
        LinkedList<Node> worklist = new LinkedList<>(cfg.getNodes());
        while (!worklist.isEmpty()) {
//            Node node = worklist.pollLast(); // ?
            Node node = worklist.pollFirst();
            Fact out_fact = analysis.newInitialFact(); // 注意后向分析(用于活变量分析)中, out集是 in集并 的直接覆盖; 而前向分析(用于常量传播)中, meetinto只改变key对应的value, 不一样
            for (Node succ :  cfg.getSuccsOf(node)) {
                analysis.meetInto(result.getInFact(succ), out_fact);
            }
            result.setOutFact(node, out_fact); // 覆盖
            if (analysis.transferNode(node, result.getInFact(node), result.getOutFact(node))) {
                worklist.addAll(cfg.getPredsOf(node));
            }
        }
    }
}
