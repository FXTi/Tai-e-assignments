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
import pascal.taie.ir.exp.InvokeExp;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.proginfo.MethodRef;
import pascal.taie.ir.stmt.*;
import pascal.taie.language.classes.ClassHierarchy;
import pascal.taie.language.classes.JMethod;
import pascal.taie.util.AnalysisException;
import pascal.taie.language.type.Type;
import pascal.taie.util.collection.Sets;

import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;
import java.util.stream.IntStream;

import static pascal.taie.analysis.graph.callgraph.CallGraphs.resolveCallee;

class Solver {

    private static final Logger logger = LogManager.getLogger(Solver.class);

    private final HeapModel heapModel;

    private DefaultCallGraph callGraph;

    private PointerFlowGraph pointerFlowGraph;

    private WorkList workList;

    private StmtProcessor stmtProcessor;

    private ClassHierarchy hierarchy;

    private final Set<Stmt> reachableStmt = Sets.newSet();

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
    private void addReachable(JMethod method) {
        if (this.callGraph.addReachableMethod(method)) {
            this.reachableStmt.addAll(method.getIR().getStmts());
            method.getIR().getStmts().stream()
                    .filter(stmt -> stmt instanceof New)
                    .map(stmt -> (New) stmt)
                    .forEach(newStmt ->
                            this.workList.addEntry(
                                    this.pointerFlowGraph.getVarPtr(newStmt.getLValue()),
                                    new PointsToSet(this.heapModel.getObj(newStmt)))
                    );
            method.getIR().getStmts().stream()
                    .filter(stmt -> stmt instanceof Copy)
                    .map(stmt -> (Copy) stmt)
                    .forEach(copy ->
                            addPFGEdge(
                                    this.pointerFlowGraph.getVarPtr(copy.getRValue()),
                                    this.pointerFlowGraph.getVarPtr(copy.getLValue()))
                    );
            method.getIR().getStmts().stream()
                    .filter(stmt -> stmt instanceof StoreField && ((StoreField) stmt).getFieldRef().isStatic())
                    .map(stmt -> (StoreField) stmt)
                    .forEach(storeField ->
                            addPFGEdge(
                                    this.pointerFlowGraph.getVarPtr(storeField.getRValue()),
                                    this.pointerFlowGraph.getStaticField(storeField.getFieldRef().resolveNullable()))
                    );
            method.getIR().getStmts().stream()
                    .filter(stmt -> stmt instanceof LoadField && ((LoadField) stmt).getFieldRef().isStatic())
                    .map(stmt -> (LoadField) stmt)
                    .forEach(loadField ->
                            addPFGEdge(
                                    this.pointerFlowGraph.getStaticField(loadField.getFieldRef().resolve()),
                                    this.pointerFlowGraph.getVarPtr(loadField.getLValue()))
                    );
            method.getIR().getStmts().stream()
                    .filter(stmt -> stmt instanceof Invoke
                            && ((Invoke) stmt).isStatic())
                    .map(stmt -> (Invoke) stmt)
                    .forEach(invoke -> {
                        JMethod m = resolveCallee(null, invoke);
                        if (this.callGraph.addEdge(new Edge<>(CallGraphs.getCallKind(invoke), invoke, m))) {
                            addReachable(m);
                            IntStream.range(0, m.getParamCount()).forEach(i -> {
                                addPFGEdge(
                                        this.pointerFlowGraph.getVarPtr(invoke.getInvokeExp().getArg(i)),
                                        this.pointerFlowGraph.getVarPtr(m.getIR().getParam(i)));
                            });
                            if (invoke.getResult() != null) {
                                m.getIR().getReturnVars().forEach(r ->
                                        addPFGEdge(
                                                this.pointerFlowGraph.getVarPtr(r),
                                                this.pointerFlowGraph.getVarPtr(invoke.getLValue()))
                                );
                            }
                        }
                    });
        }
    }

    /**
     * Processes statements in new reachable methods.
     */
    private class StmtProcessor implements StmtVisitor<Void> {
        // TODO - if you choose to implement addReachable()
        //  via visitor pattern, then finish me
    }

    /**
     * Adds an edge "source -> target" to the PFG.
     */
    private void addPFGEdge(Pointer source, Pointer target) {
        if (this.pointerFlowGraph.addEdge(source, target)) {
            if (!source.getPointsToSet().isEmpty()) {
                this.workList.addEntry(target, source.getPointsToSet());
            }
        }
    }

    /**
     * Processes work-list entries until the work-list is empty.
     */
    private void analyze() {
        while (!this.workList.isEmpty()) {
            WorkList.Entry entry = this.workList.pollEntry();
            PointsToSet delta = propagate(entry.pointer(), entry.pointsToSet());
            if (entry.pointer() instanceof VarPtr) {
                final Var var = ((VarPtr) entry.pointer()).getVar();
                for (Obj o : delta) {
                    var.getStoreFields().stream()
                            .filter(storeField -> this.reachableStmt.contains(storeField))
                            .forEach(storeField ->
                                    addPFGEdge(
                                            this.pointerFlowGraph.getVarPtr(storeField.getRValue()),
                                            storeField.isStatic()
                                            ? this.pointerFlowGraph.getStaticField(storeField.getFieldRef().resolve())
                                            : this.pointerFlowGraph.getInstanceField(o, storeField.getFieldRef().resolve()))
                            );
                    var.getLoadFields().stream()
                            .filter(loadField -> this.reachableStmt.contains(loadField))
                            .forEach(loadField ->
                                    addPFGEdge(
                                            loadField.isStatic()
                                            ? this.pointerFlowGraph.getStaticField(loadField.getFieldRef().resolve())
                                            : this.pointerFlowGraph.getInstanceField(o, loadField.getFieldRef().resolve()),
                                            this.pointerFlowGraph.getVarPtr(loadField.getLValue()))
                            );
                    var.getLoadArrays().stream()
                            .filter(loadArray -> this.reachableStmt.contains(loadArray))
                            .forEach(loadArray ->
                                    addPFGEdge(
                                            this.pointerFlowGraph.getArrayIndex(o),
                                            this.pointerFlowGraph.getVarPtr(loadArray.getLValue())
                                    )
                            );
                    var.getStoreArrays().stream()
                            .filter(storeArray -> this.reachableStmt.contains(storeArray))
                            .forEach(storeArray ->
                                    addPFGEdge(
                                            this.pointerFlowGraph.getVarPtr(storeArray.getRValue()),
                                            this.pointerFlowGraph.getArrayIndex(o)
                                    )
                            );
                    processCall(var, o);
                }
            }
        }
    }

    /**
     * Propagates pointsToSet to pt(pointer) and its PFG successors,
     * returns the difference set of pointsToSet and pt(pointer).
     */
    private PointsToSet propagate(Pointer pointer, PointsToSet pointsToSet) {
        PointsToSet delta = new PointsToSet();
        pointsToSet.objects()
                .filter(o -> !pointer.getPointsToSet().contains(o))
                .forEach(delta::addObject);

        if (!delta.isEmpty()) {
            delta.forEach(pointer.getPointsToSet()::addObject);
            this.pointerFlowGraph.getSuccsOf(pointer).forEach(p -> this.workList.addEntry(p, delta));
        }
        return delta;
    }

    /**
     * Processes instance calls when points-to set of the receiver variable changes.
     *
     * @param var the variable that holds receiver objects
     * @param recv a new discovered object pointed by the variable.
     */
    private void processCall(Var var, Obj recv) {
        for (Invoke invoke : var.getInvokes().stream()
                .filter(i -> this.reachableStmt.contains(i)).collect(Collectors.toList())) {
            JMethod method = resolveCallee(recv, invoke);
            this.workList.addEntry(this.pointerFlowGraph.getVarPtr(method.getIR().getThis()), new PointsToSet(recv));
            if (this.callGraph.addEdge(new Edge<>(CallGraphs.getCallKind(invoke), invoke, method))) {
                addReachable(method);
                IntStream.range(0, method.getParamCount()).forEach(i -> {
                    addPFGEdge(
                            this.pointerFlowGraph.getVarPtr(invoke.getInvokeExp().getArg(i)),
                            this.pointerFlowGraph.getVarPtr(method.getIR().getParam(i)));
                });
                if (invoke.getResult() != null) {
                    method.getIR().getReturnVars().forEach(r ->
                            addPFGEdge(
                                    this.pointerFlowGraph.getVarPtr(r),
                                    this.pointerFlowGraph.getVarPtr(invoke.getLValue()))
                    );
                }
            }
        }
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
