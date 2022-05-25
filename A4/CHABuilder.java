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
import java.util.stream.Collectors;
import java.util.stream.Stream;

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
        Stack<JMethod> workList = new Stack() {{ add(entry); }};
        while (!workList.isEmpty()) {
            JMethod curr = workList.pop();
            if (!callGraph.contains(curr)) {
                callGraph.addReachableMethod(curr);
                callGraph.callSitesIn(curr).forEach(cs -> {
                    resolve(cs).stream().forEach(m -> {
                        callGraph.addEdge(new Edge<>(CallGraphs.getCallKind(cs), cs, m));
                        workList.add(m);
                    });
                });
            }
        }
        return callGraph;
    }

    /**
     * Resolves call targets (callees) of a call site via CHA.
     */
    private Set<JMethod> resolve(Invoke callSite) {
        MethodRef methodRef = callSite.getMethodRef();
        switch (CallGraphs.getCallKind(callSite)) {
            case STATIC: return Collections.singleton(methodRef.getDeclaringClass().getDeclaredMethod(methodRef.getSubsignature()));
            case SPECIAL: return Collections.singleton(dispatch(methodRef.getDeclaringClass(), methodRef.getSubsignature())).stream()
                    .filter(m -> m != null)
                    .collect(Collectors.toSet());
            case INTERFACE:
            case VIRTUAL: {
                Set<JMethod> result = new HashSet<>();
                Stack<JClass> todo = new Stack<>() {{ add(methodRef.getDeclaringClass()); }};
                while (!todo.isEmpty()) {
                    JClass curr = todo.pop();
                    if (dispatch(curr, methodRef.getSubsignature()) != null) {
                        result.add(dispatch(curr, methodRef.getSubsignature()));
                    }
                    if (curr.isInterface()) {
                        todo.addAll(hierarchy.getDirectImplementorsOf(curr));
                        todo.addAll(hierarchy.getDirectSubinterfacesOf(curr));
                    } else {
                        todo.addAll(hierarchy.getDirectSubclassesOf(curr));
                    }
                }
                return result;
            }
        }
        return Collections.EMPTY_SET;
    }

    /**
     * Looks up the target method based on given class and method subsignature.
     *
     * @return the dispatched target method, or null if no satisfying method
     * can be found.
     */
    private JMethod dispatch(JClass jclass, Subsignature subsignature) {
        while (jclass != null && (jclass.getDeclaredMethod(subsignature) == null
                || jclass.getDeclaredMethod(subsignature).isAbstract())) {
            jclass = jclass.getSuperClass();
        }
        return (jclass != null && jclass.getDeclaredMethod(subsignature) != null
                && !jclass.getDeclaredMethod(subsignature).isAbstract())
                    ? jclass.getDeclaredMethod(subsignature)
                    : null;
    }
}