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

package pascal.taie.analysis.graph.callgraph;

import pascal.taie.World;
import pascal.taie.ir.proginfo.MethodRef;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.language.classes.ClassHierarchy;
import pascal.taie.language.classes.JClass;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.classes.Subsignature;

import java.util.*;

/**
 * Implementation of the CHA algorithm.
 */
class CHABuilder implements CGBuilder<Invoke, JMethod> {

    private ClassHierarchy hierarchy;

    @Override
    public CallGraph<Invoke, JMethod> build() {
        hierarchy = World.get().getClassHierarchy();
        return buildCallGraph(World.get().getMainMethod());
    }

    private CallGraph<Invoke, JMethod> buildCallGraph(JMethod entry) {
        DefaultCallGraph callGraph = new DefaultCallGraph();
        callGraph.addEntryMethod(entry);
        // TODO - finish me
        Queue<JMethod> workList = new LinkedList<>();
        workList.add(entry);
        while (!workList.isEmpty()) {
            JMethod jMethod = workList.poll();
            if (callGraph.contains(jMethod)) { // 在当前调用图已可达
                continue;
            }
            callGraph.addReachableMethod(jMethod);

            callGraph.callSitesIn(jMethod).forEach(callSite -> {
                for (JMethod targetMethod : resolve(callSite)) {
                    callGraph.addEdge(new Edge<>(CallGraphs.getCallKind(callSite), callSite, targetMethod));
                    workList.add(targetMethod);
                }
            });
        }

        return callGraph;
    }

    /**
     * Resolves call targets (callees) of a call site via CHA.
     */
    private Set<JMethod> resolve(Invoke callSite) {
        // TODO - finish me
        Set<JMethod> T = new HashSet<>();
        MethodRef methodRef = callSite.getMethodRef();
        // or use callSite.isStatic()
        switch (CallGraphs.getCallKind(callSite)) {
            case STATIC -> T.add(methodRef.getDeclaringClass().getDeclaredMethod(methodRef.getSubsignature()));
            case SPECIAL -> {
                JMethod jMethod = dispatch(methodRef.getDeclaringClass(), methodRef.getSubsignature());
                if (jMethod != null) {
                    T.add(jMethod);
                }
            }
            case VIRTUAL, INTERFACE -> {
                Queue<JClass> queue = new LinkedList<>();
                queue.add(methodRef.getDeclaringClass());
                while (!queue.isEmpty()) {
                    JClass jClass = queue.poll();
                    JMethod dispatchedMethod = dispatch(jClass, methodRef.getSubsignature());
                    if (dispatchedMethod != null) {
                        T.add(dispatchedMethod);
                    }

                    if (jClass.isInterface()) {
                        queue.addAll(hierarchy.getDirectSubinterfacesOf(jClass));
                        queue.addAll(hierarchy.getDirectImplementorsOf(jClass));
                    } else {
                        queue.addAll(hierarchy.getDirectSubclassesOf(jClass));
                    }
                }
            }
        }

        return T;
    }

    /**
     * Looks up the target method based on given class and method subsignature.
     *
     * @return the dispatched target method, or null if no satisfying method
     * can be found.
     */
    private JMethod dispatch(JClass jclass, Subsignature subsignature) {
        // TODO - finish me
        JMethod jMethod = jclass.getDeclaredMethod(subsignature);
        if (jMethod != null && !jMethod.isAbstract()) { // 找到对应方法且不是抽象方法
            return jMethod;
        } else if (jclass.getSuperClass() != null) { // 当前类里没有符合条件的方法, 若有父类, 去父类找
            return dispatch(jclass.getSuperClass(), subsignature);
        } else {
            return null;
        }
    }
}
