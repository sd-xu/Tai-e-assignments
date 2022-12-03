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

package pascal.taie.analysis.pta.ci;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.World;
import pascal.taie.analysis.graph.callgraph.CallGraphs;
import pascal.taie.analysis.graph.callgraph.CallKind;
import pascal.taie.analysis.graph.callgraph.DefaultCallGraph;
import pascal.taie.analysis.graph.callgraph.Edge;
import pascal.taie.analysis.pta.core.heap.HeapModel;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.*;
import pascal.taie.language.classes.ClassHierarchy;
import pascal.taie.language.classes.JField;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.type.Type;

import java.util.List;

class Solver {

    private static final Logger logger = LogManager.getLogger(Solver.class);

    private final HeapModel heapModel;

    private DefaultCallGraph callGraph;

    private PointerFlowGraph pointerFlowGraph;

    private WorkList workList;

    private StmtProcessor stmtProcessor;

    private ClassHierarchy hierarchy;

    Solver(HeapModel heapModel) {
        this.heapModel = heapModel;
    }

    /**
     * Runs pointer analysis algorithm.
     */
    void solve() {
        initialize();
        analyze();
    }

    /**
     * Initializes pointer analysis.
     */
    private void initialize() {
        workList = new WorkList();
        pointerFlowGraph = new PointerFlowGraph();
        callGraph = new DefaultCallGraph();
        stmtProcessor = new StmtProcessor();
        hierarchy = World.get().getClassHierarchy();
        // initialize main method
        JMethod main = World.get().getMainMethod();
        callGraph.addEntryMethod(main);
        addReachable(main);
    }

    /**
     * Processes new reachable method.
     */
    private void addReachable(JMethod method) { // 不要忘记在该方法中处理静态字段 loads/stores 和静态方法调用
        // TODO - finish me
        if (!callGraph.contains(method)) {
            callGraph.addReachableMethod(method);
            // 对方法中的每条语句处理(访问者模式)
            method.getIR().getStmts().forEach(stmt -> stmt.accept(stmtProcessor));
        }
    }

    /**
     * Processes statements in new reachable methods.
     */
    private class StmtProcessor implements StmtVisitor<Void> {
        // TODO - if you choose to implement addReachable()
        //  via visitor pattern, then finish me

        @Override
        public Void visit(New stmt) {  // New语句
            // 获取变量对应的指针
            Pointer ptr = pointerFlowGraph.getVarPtr(stmt.getLValue());
            // 获取New语句对应的抽象对象
            Obj obj = heapModel.getObj(stmt);
            // 生成指针对应的指针集
            PointsToSet pointsToSet = new PointsToSet(obj);
            // add <x, {oi}> to WL
            workList.addEntry(ptr, pointsToSet);
            return null;
        }

        @Override
        public Void visit(Copy stmt) { // Copy语句
            // VarPtr继承Pointer
            Pointer rValuePtr = pointerFlowGraph.getVarPtr(stmt.getRValue());

            Pointer lvaluePtr = pointerFlowGraph.getVarPtr(stmt.getLValue());

            // AddEdge(y, x)
            addPFGEdge(rValuePtr, lvaluePtr);
            return null;
        }

        @Override
        public Void visit(Invoke callSite) { // 静态Invoke语句
            if (callSite.isStatic()) {
                JMethod callee = resolveCallee(null, callSite);
                processSingleCall(callSite, callee);
            }
            return null;
        }

        @Override
        public Void visit(LoadField stmt) { // 静态字段LoadField语句
            if (stmt.isStatic()) {
                // 获取LoadField语句要load的字段
                JField field = stmt.getFieldRef().resolve();
                // StaticField继承Pointer
                Pointer rValuePtr = pointerFlowGraph.getStaticField(field);

                Pointer lvaluePtr = pointerFlowGraph.getVarPtr(stmt.getLValue());

                addPFGEdge(rValuePtr, lvaluePtr);
            }
            return null;
        }

        @Override
        public Void visit(StoreField stmt) { // 静态字段StoreField语句
            if (stmt.isStatic()) {
                Pointer rValuePtr = pointerFlowGraph.getVarPtr(stmt.getRValue());

                // 获取StoreField语句要store的字段
                JField field = stmt.getFieldRef().resolve();
                // StaticField继承Pointer
                Pointer lValuePtr = pointerFlowGraph.getStaticField(field);

                addPFGEdge(rValuePtr, lValuePtr);
            }
            return null;
        }
    }

    /**
     * Adds an edge "source -> target" to the PFG.
     */
    private void addPFGEdge(Pointer source, Pointer target) {
        // TODO - finish me
        if (!pointerFlowGraph.getSuccsOf(source).contains(target)) {
            pointerFlowGraph.addEdge(source, target);
            PointsToSet pts = source.getPointsToSet();
            if (!pts.isEmpty()) {
                workList.addEntry(target, pts);
            }
        }
    }

    /**
     * Processes work-list entries until the work-list is empty.
     */
    private void analyze() { // 不要忘记在这个方法中处理数组 loads/stores
        // TODO - finish me
        while (!workList.isEmpty()) {
            // 内部 Record 类 Entry 表示 worklist 中的条目
            WorkList.Entry entry = workList.pollEntry();
            Pointer pointer = entry.pointer();
            PointsToSet pts = entry.pointsToSet();
            // △ = pts - pt(n)
            PointsToSet delta = propagate(pointer, pts);
            if (pointer instanceof VarPtr ptr) {
                Var var = ptr.getVar();
                delta.forEach(obj -> {
                    // 实例字段StoreField
                    var.getStoreFields().forEach(stmt -> {
                        addPFGEdge(
                                pointerFlowGraph.getVarPtr(stmt.getRValue()),
                                pointerFlowGraph.getInstanceField(obj, stmt.getFieldRef().resolve())
                        );
                    });
                    // 实例字段LoadField
                    var.getLoadFields().forEach(stmt -> {
                        addPFGEdge(
                                pointerFlowGraph.getInstanceField(obj, stmt.getFieldRef().resolve()),
                                pointerFlowGraph.getVarPtr(stmt.getLValue())
                        );
                    });
                    // StoreArray
                    var.getStoreArrays().forEach(stmt -> {
                        addPFGEdge(
                                pointerFlowGraph.getVarPtr(stmt.getRValue()),
                                pointerFlowGraph.getArrayIndex(obj)
                        );
                    });
                    // LoadArray
                    var.getLoadArrays().forEach(stmt -> {
                        addPFGEdge(
                                pointerFlowGraph.getArrayIndex(obj),
                                pointerFlowGraph.getVarPtr(stmt.getLValue())
                        );
                    });
                    // ProcessCall
                    processCall(var, obj);
                });
            }
        }
    }

    /**
     * Propagates pointsToSet to pt(pointer) and its PFG successors,
     * returns the difference set of pointsToSet and pt(pointer).
     */
    private PointsToSet propagate(Pointer pointer, PointsToSet pointsToSet) {
        // TODO - finish me
        PointsToSet delta = new PointsToSet();
        // △ = pts - pt(n)
        pointsToSet.objects()
                .filter(ptr -> !pointer.getPointsToSet().contains(ptr))
                .forEach(delta::addObject);
        if (!delta.isEmpty()) {
            // pt(n) ∪= △
            delta.forEach(obj -> pointer.getPointsToSet().addObject(obj));
            // n -> s: add <s, △> to WL
            pointerFlowGraph.getSuccsOf(pointer).forEach(succ -> workList.addEntry(succ, delta));
        }
        return delta;
    }

    /**
     * 处理静态调用
     * 处理所有种类的实例方法调用, 即虚调用、接口调用和特殊调用
     */
    private void processSingleCall(Invoke callSite, JMethod callee) {
        if (!callGraph.getCalleesOf(callSite).contains(callee)) {
            CallKind callKind = CallGraphs.getCallKind(callSite);
            switch (callKind) {
                case STATIC, VIRTUAL, INTERFACE, SPECIAL -> {
                    callGraph.addEdge(new Edge<>(callKind, callSite, callee));
                    addReachable(callee);
                    List<Var> args = callee.getIR().getParams();
                    // assert args.size() == callSite.getRValue().getArgs().size();
                    for (int i = 0; i < args.size(); i++) {
                        addPFGEdge(
                                pointerFlowGraph.getVarPtr(callSite.getRValue().getArg(i)),
                                pointerFlowGraph.getVarPtr(args.get(i))
                        );
                    }
                    if (callSite.getLValue() != null) {
                        callee.getIR().getReturnVars().forEach(ret -> {
                            addPFGEdge(
                                    pointerFlowGraph.getVarPtr(ret),
                                    pointerFlowGraph.getVarPtr(callSite.getLValue())
                            );
                        });
                    }
                }
            }
        }
    }

    /**
     * Processes instance calls when points-to set of the receiver variable changes.
     *
     * @param var the variable that holds receiver objects
     * @param recv a new discovered object pointed by the variable.
     */
    private void processCall(Var var, Obj recv) {
        // TODO - finish me
        var.getInvokes().forEach(callSite -> {
            // dispatch
            JMethod callee = resolveCallee(recv, callSite);
            // add <m_this, {oi}> to WL
            VarPtr mThisPtr = pointerFlowGraph.getVarPtr(callee.getIR().getThis());
            workList.addEntry(mThisPtr, new PointsToSet(recv));
            processSingleCall(callSite, callee);
        });
    }

    /**
     * Resolves the callee of a call site with the receiver object.
     *
     * @param recv     the receiver object of the method call. If the callSite
     *                 is static, this parameter is ignored (i.e., can be null).
     * @param callSite the call site to be resolved.
     * @return the resolved callee.
     */
    private JMethod resolveCallee(Obj recv, Invoke callSite) {
        Type type = recv != null ? recv.getType() : null;
        return CallGraphs.resolveCallee(type, callSite);
    }

    CIPTAResult getResult() {
        return new CIPTAResult(pointerFlowGraph, callGraph);
    }
}
