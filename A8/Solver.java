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

package pascal.taie.analysis.pta.cs;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.World;
import pascal.taie.analysis.graph.callgraph.CallGraphs;
import pascal.taie.analysis.graph.callgraph.CallKind;
import pascal.taie.analysis.graph.callgraph.Edge;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.analysis.pta.PointerAnalysisResultImpl;
import pascal.taie.analysis.pta.core.cs.CSCallGraph;
import pascal.taie.analysis.pta.core.cs.context.Context;
import pascal.taie.analysis.pta.core.cs.element.ArrayIndex;
import pascal.taie.analysis.pta.core.cs.element.CSCallSite;
import pascal.taie.analysis.pta.core.cs.element.CSManager;
import pascal.taie.analysis.pta.core.cs.element.CSMethod;
import pascal.taie.analysis.pta.core.cs.element.CSObj;
import pascal.taie.analysis.pta.core.cs.element.CSVar;
import pascal.taie.analysis.pta.core.cs.element.InstanceField;
import pascal.taie.analysis.pta.core.cs.element.MapBasedCSManager;
import pascal.taie.analysis.pta.core.cs.element.Pointer;
import pascal.taie.analysis.pta.core.cs.element.StaticField;
import pascal.taie.analysis.pta.core.cs.selector.ContextSelector;
import pascal.taie.analysis.pta.core.heap.HeapModel;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.analysis.pta.plugin.taint.TaintAnalysiss;
import pascal.taie.analysis.pta.pts.PointsToSet;
import pascal.taie.analysis.pta.pts.PointsToSetFactory;
import pascal.taie.config.AnalysisOptions;
import pascal.taie.ir.exp.InvokeExp;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.*;
import pascal.taie.language.classes.JField;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.type.Type;
import pascal.taie.util.collection.Sets;

import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;
import java.util.stream.IntStream;

public class Solver {

    private static final Logger logger = LogManager.getLogger(Solver.class);

    private final AnalysisOptions options;

    private final HeapModel heapModel;

    private final ContextSelector contextSelector;

    private CSManager csManager;

    private CSCallGraph callGraph;

    private PointerFlowGraph pointerFlowGraph;

    private PointerFlowGraph taintPointerFlowGraph;

    private WorkList workList;

    private TaintAnalysiss taintAnalysis;

    private PointerAnalysisResult result;

    private final Set<Stmt> reachableStmt = Sets.newSet();

    Solver(AnalysisOptions options, HeapModel heapModel,
           ContextSelector contextSelector) {
        this.options = options;
        this.heapModel = heapModel;
        this.contextSelector = contextSelector;
    }

    public AnalysisOptions getOptions() {
        return options;
    }

    public ContextSelector getContextSelector() {
        return contextSelector;
    }

    public CSManager getCSManager() {
        return csManager;
    }

    void solve() {
        initialize();
        analyze();
        taintAnalysis.onFinish();
    }

    public CSCallGraph getCallGraph() {
        return this.callGraph;
    }

    private void initialize() {
        csManager = new MapBasedCSManager();
        callGraph = new CSCallGraph(csManager);
        pointerFlowGraph = new PointerFlowGraph();
        taintPointerFlowGraph = new PointerFlowGraph();
        workList = new WorkList();
        taintAnalysis = new TaintAnalysiss(this);
        // process program entry, i.e., main method
        Context defContext = contextSelector.getEmptyContext();
        JMethod main = World.get().getMainMethod();
        CSMethod csMethod = csManager.getCSMethod(defContext, main);
        callGraph.addEntryMethod(csMethod);
        addReachable(csMethod);
    }

    /**
     * Processes new reachable context-sensitive method.
     */
    private void addReachable(CSMethod csMethod) {
        if (this.callGraph.addReachableMethod(csMethod)) {
            this.reachableStmt.addAll(csMethod.getMethod().getIR().getStmts());
            csMethod.getMethod().getIR().getStmts().stream()
                    .filter(stmt -> stmt instanceof New)
                    .map(stmt -> (New) stmt)
                    .forEach(newStmt -> {
                        final Obj o = this.heapModel.getObj(newStmt);
                        final Context c = this.contextSelector.selectHeapContext(csMethod, o);
                        this.workList.addEntry(
                                this.csManager.getCSVar(csMethod.getContext(), newStmt.getLValue()),
                                PointsToSetFactory.make(this.csManager.getCSObj(c, o)));
                    });
            csMethod.getMethod().getIR().getStmts().stream()
                    .filter(stmt -> stmt instanceof Copy)
                    .map(stmt -> (Copy) stmt)
                    .forEach(copy ->
                            addPFGEdge(
                                    this.csManager.getCSVar(csMethod.getContext(), copy.getRValue()),
                                    this.csManager.getCSVar(csMethod.getContext(), copy.getLValue()))
                    );
            csMethod.getMethod().getIR().getStmts().stream()
                    .filter(stmt -> stmt instanceof StoreField && ((StoreField) stmt).getFieldRef().isStatic())
                    .map(stmt -> (StoreField) stmt)
                    .forEach(storeField ->
                            addPFGEdge(
                                    this.csManager.getCSVar(csMethod.getContext(), storeField.getRValue()),
                                    this.csManager.getStaticField(storeField.getFieldRef().resolve()))
                    );
            csMethod.getMethod().getIR().getStmts().stream()
                    .filter(stmt -> stmt instanceof LoadField && ((LoadField) stmt).getFieldRef().isStatic())
                    .map(stmt -> (LoadField) stmt)
                    .forEach(loadField ->
                            addPFGEdge(
                                    this.csManager.getStaticField(loadField.getFieldRef().resolve()),
                                    this.csManager.getCSVar(csMethod.getContext(), loadField.getLValue()))
                    );
            csMethod.getMethod().getIR().getStmts().stream()
                    .filter(stmt -> stmt instanceof Invoke
                            && ((Invoke) stmt).isStatic())
                    .map(stmt -> (Invoke) stmt)
                    .forEach(invoke -> {
                        JMethod m = resolveCallee(null, invoke);
                        CSCallSite csCallSite = this.csManager.getCSCallSite(csMethod.getContext(), invoke);
                        Context ct = this.contextSelector.selectContext(csCallSite, m);
                        CSMethod ctm = this.csManager.getCSMethod(ct, m);
                        if (this.callGraph.addEdge(new Edge<>(CallGraphs.getCallKind(invoke), csCallSite, ctm))) {
                            addReachable(ctm);
                            IntStream.range(0, m.getParamCount()).forEach(i -> {
                                addPFGEdge(
                                        this.csManager.getCSVar(csMethod.getContext(), invoke.getInvokeExp().getArg(i)),
                                        this.csManager.getCSVar(ct, m.getIR().getParam(i)));
                            });
                            if (invoke.getResult() != null) {
                                m.getIR().getReturnVars().forEach(r ->
                                        addPFGEdge(
                                                this.csManager.getCSVar(ct, r),
                                                this.csManager.getCSVar(csMethod.getContext(), invoke.getLValue()))
                                );
                                if (this.taintAnalysis.isSource(m, invoke.getLValue().getType())) {
                                    this.workList.addEntry(
                                            this.csManager.getCSVar(csMethod.getContext(), invoke.getLValue()),
                                            PointsToSetFactory.make(this.taintAnalysis.makeTaint(invoke)));
                                }
                                this.taintAnalysis.getArgToResultTransfers(m, invoke.getLValue().getType())
                                        .forEach(to ->
                                                addTaintPFGEdge(
                                                        this.csManager.getCSVar(csMethod.getContext(), invoke.getInvokeExp().getArg(to)),
                                                        this.csManager.getCSVar(csMethod.getContext(), invoke.getLValue())
                                                )
                                );
                            }
                        }
                    });
        }
    }

    /**
     * Processes the statements in context-sensitive new reachable methods.
     */
    private class StmtProcessor implements StmtVisitor<Void> {

        private final CSMethod csMethod;

        private final Context context;

        private StmtProcessor(CSMethod csMethod) {
            this.csMethod = csMethod;
            this.context = csMethod.getContext();
        }

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

    private void addTaintPFGEdge(Pointer source, Pointer target) {
        if (this.taintPointerFlowGraph.addEdge(source, target)) {
            PointsToSet tmp = this.taintAnalysis.getTaintPointsToSet(source.getPointsToSet());
            if (!tmp.isEmpty()) {
                this.workList.addEntry(target, tmp);
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
            if (entry.pointer() instanceof CSVar) {
                final Var var = ((CSVar) entry.pointer()).getVar();
                for (CSObj o : delta.objects().filter(o -> !this.taintAnalysis.isTaint(o.getObject()))
                        .collect(Collectors.toList())) {
                    var.getStoreFields().stream()
                            .filter(storeField -> this.reachableStmt.contains(storeField))
                            .forEach(storeField ->
                                    addPFGEdge(
                                            this.csManager.getCSVar(((CSVar) entry.pointer()).getContext(), storeField.getRValue()),
                                            storeField.isStatic()
                                                    ? this.csManager.getStaticField(storeField.getFieldRef().resolve())
                                                    : this.csManager.getInstanceField(o, storeField.getFieldRef().resolve()))
                            );
                    var.getLoadFields().stream()
                            .filter(loadField -> this.reachableStmt.contains(loadField))
                            .forEach(loadField ->
                                    addPFGEdge(
                                            loadField.isStatic()
                                                    ? this.csManager.getStaticField(loadField.getFieldRef().resolve())
                                                    : this.csManager.getInstanceField(o, loadField.getFieldRef().resolve()),
                                            this.csManager.getCSVar(((CSVar) entry.pointer()).getContext(), loadField.getLValue()))
                            );
                    var.getLoadArrays().stream()
                            .filter(loadArray -> this.reachableStmt.contains(loadArray))
                            .forEach(loadArray ->
                                    addPFGEdge(
                                            this.csManager.getArrayIndex(o),
                                            this.csManager.getCSVar(((CSVar) entry.pointer()).getContext(), loadArray.getLValue())
                                    )
                            );
                    var.getStoreArrays().stream()
                            .filter(storeArray -> this.reachableStmt.contains(storeArray))
                            .forEach(storeArray ->
                                    addPFGEdge(
                                            this.csManager.getCSVar(((CSVar) entry.pointer()).getContext(), storeArray.getRValue()),
                                            this.csManager.getArrayIndex(o)
                                    )
                            );
                    processCall((CSVar) entry.pointer(), o);
                }
            }
        }
    }

    /**
     * Propagates pointsToSet to pt(pointer) and its PFG successors,
     * returns the difference set of pointsToSet and pt(pointer).
     */
    private PointsToSet propagate(Pointer pointer, PointsToSet pointsToSet) {
        PointsToSet delta = PointsToSetFactory.make();
        pointsToSet.objects()
                .filter(o -> !pointer.getPointsToSet().contains(o))
                .forEach(delta::addObject);

        if (!delta.isEmpty()) {
            delta.forEach(pointer.getPointsToSet()::addObject);
            this.pointerFlowGraph.getSuccsOf(pointer).forEach(p -> this.workList.addEntry(p, delta));
            this.taintPointerFlowGraph.getSuccsOf(pointer)
                    .forEach(p -> this.workList.addEntry(p, this.taintAnalysis.getTaintPointsToSet(delta)));
        }
        return delta;
    }

    /**
     * Processes instance calls when points-to set of the receiver variable changes.
     *
     * @param recv    the receiver variable
     * @param recvObj set of new discovered objects pointed by the variable.
     */
    private void processCall(CSVar recv, CSObj recvObj) {
        for (Invoke invoke : recv.getVar().getInvokes().stream()
                .filter(i -> this.reachableStmt.contains(i)).collect(Collectors.toList())) {
            JMethod method = resolveCallee(recvObj, invoke);
            CSCallSite csCallSite = this.csManager.getCSCallSite(recv.getContext(), invoke);
            Context ct = this.contextSelector.selectContext(csCallSite, recvObj, method);
            CSMethod ctm = this.csManager.getCSMethod(ct, method);
            this.workList.addEntry(this.csManager.getCSVar(ct, method.getIR().getThis()), PointsToSetFactory.make(recvObj));
            if (this.callGraph.addEdge(new Edge<>(CallGraphs.getCallKind(invoke), csCallSite, ctm))) {
                addReachable(ctm);
                IntStream.range(0, method.getParamCount()).forEach(i -> {
                    addPFGEdge(
                            this.csManager.getCSVar(recv.getContext(), invoke.getInvokeExp().getArg(i)),
                            this.csManager.getCSVar(ct, method.getIR().getParam(i)));
                });

                this.taintAnalysis.getArgToBaseTransfers(method, recv.getType())
                        .forEach(from ->
                                addTaintPFGEdge(
                                        this.csManager.getCSVar(recv.getContext(), invoke.getInvokeExp().getArg(from)),
                                        recv
                                )
                        );

                if (invoke.getResult() != null) {
                    method.getIR().getReturnVars().forEach(r ->
                            addPFGEdge(
                                    this.csManager.getCSVar(ct, r),
                                    this.csManager.getCSVar(recv.getContext(), invoke.getLValue()))
                    );
                    if (this.taintAnalysis.isSource(method, invoke.getLValue().getType())) {
                        this.workList.addEntry(
                                this.csManager.getCSVar(recv.getContext(), invoke.getLValue()),
                                PointsToSetFactory.make(this.taintAnalysis.makeTaint(invoke)));
                    }
                    this.taintAnalysis.getArgToResultTransfers(method, invoke.getLValue().getType())
                            .forEach(from ->
                                    addTaintPFGEdge(
                                            this.csManager.getCSVar(recv.getContext(), invoke.getInvokeExp().getArg(from)),
                                            this.csManager.getCSVar(recv.getContext(), invoke.getLValue())
                                    )
                            );
                    this.taintAnalysis.getBaseToResultTransfers(method, invoke.getLValue().getType())
                            .forEach(__ ->
                                    addTaintPFGEdge(
                                            recv,
                                            this.csManager.getCSVar(recv.getContext(), invoke.getLValue())
                                    )
                            );
                }
            }
        }
    }

    /**
     * Resolves the callee of a call site with the receiver object.
     *
     * @param recv the receiver object of the method call. If the callSite
     *             is static, this parameter is ignored (i.e., can be null).
     * @param callSite the call site to be resolved.
     * @return the resolved callee.
     */
    private JMethod resolveCallee(CSObj recv, Invoke callSite) {
        Type type = recv != null ? recv.getObject().getType() : null;
        return CallGraphs.resolveCallee(type, callSite);
    }

    public PointerAnalysisResult getResult() {
        if (result == null) {
            result = new PointerAnalysisResultImpl(csManager, callGraph);
        }
        return result;
    }
}
