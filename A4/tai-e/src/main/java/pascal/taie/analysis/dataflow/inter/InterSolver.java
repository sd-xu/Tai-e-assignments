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

package pascal.taie.analysis.dataflow.inter;

import pascal.taie.analysis.dataflow.fact.DataflowResult;
import pascal.taie.analysis.graph.icfg.ICFG;
import pascal.taie.analysis.graph.icfg.ICFGEdge;
import pascal.taie.util.collection.SetQueue;

import java.util.LinkedList;
import java.util.Queue;
import java.util.Set;
import java.util.stream.Collectors;

/**
 * Solver for inter-procedural data-flow analysis.
 * The workload of inter-procedural analysis is heavy, thus we always
 * adopt work-list algorithm for efficiency.
 */
class InterSolver<Method, Node, Fact> {

    private final InterDataflowAnalysis<Node, Fact> analysis;

    private final ICFG<Method, Node> icfg;

    private DataflowResult<Node, Fact> result;

    private Queue<Node> workList;

    InterSolver(InterDataflowAnalysis<Node, Fact> analysis,
                ICFG<Method, Node> icfg) {
        this.analysis = analysis;
        this.icfg = icfg;
    }

    DataflowResult<Node, Fact> solve() {
        result = new DataflowResult<>();
        initialize();
        doSolve();
        return result;
    }

    private void initialize() {
        // TODO - finish me
        // 初始化程序中所有的 IN/OUT fact
        for (Node node : icfg) {
            result.setInFact(node, analysis.newInitialFact());
            result.setOutFact(node, analysis.newInitialFact());
        }
        // 仅需对 ICFG 的 entry 方法的 entry 节点设置 boundary fact(覆盖前面的initial)
        icfg.entryMethods().forEach(entryMethod -> {
            Node entryNode = icfg.getEntryOf(entryMethod);
            result.setInFact(entryNode, analysis.newBoundaryFact(entryNode));
            result.setOutFact(entryNode, analysis.newBoundaryFact(entryNode));
        });
    }

    private void doSolve() {
        // TODO - finish me
        Queue<Node> workList = new LinkedList<>(icfg.getNodes());

        while (!workList.isEmpty()) {
            Node node = workList.poll();
            Fact in = result.getInFact(node);
            Fact out = result.getOutFact(node);
            // 先对该节点的前驱的 OUT fact 应用 edge transfer，然后把得到结果 meet 进该节点的 IN fact
            for (ICFGEdge<Node> edge : icfg.getInEdgesOf(node)) {
                analysis.meetInto(analysis.transferEdge(edge, result.getOutFact(edge.getSource())), in);
            }
            // 如果发生了改变, 把所有后继加入WL
            if (analysis.transferNode(node, in, out)) {
                icfg.getSuccsOf(node).forEach(workList::offer);
            }
        }
    }
}
