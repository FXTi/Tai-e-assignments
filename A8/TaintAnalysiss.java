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

package pascal.taie.analysis.pta.plugin.taint;

import com.google.common.collect.HashMultimap;
import com.google.common.collect.Multimap;
import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.World;
import pascal.taie.analysis.graph.callgraph.Edge;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.analysis.pta.core.cs.context.Context;
import pascal.taie.analysis.pta.core.cs.element.*;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.analysis.pta.cs.Solver;
import pascal.taie.analysis.pta.pts.PointsToSet;
import pascal.taie.analysis.pta.pts.PointsToSetFactory;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.type.Type;

import java.util.*;
import java.util.stream.Collectors;
import java.util.stream.Stream;

public class TaintAnalysiss {

    private static final Logger logger = LogManager.getLogger(TaintAnalysiss.class);

    private final TaintManager manager;

    private final TaintConfig config;

    private final Solver solver;

    private final CSManager csManager;

    private final Context emptyContext;

    public TaintAnalysiss(Solver solver) {
        manager = new TaintManager();
        this.solver = solver;
        csManager = solver.getCSManager();
        emptyContext = solver.getContextSelector().getEmptyContext();
        config = TaintConfig.readConfig(
                solver.getOptions().getString("taint-config"),
                World.get().getClassHierarchy(),
                World.get().getTypeSystem());
        logger.info(config);
    }

    // TODO - finish me

    public void onFinish() {
        Set<TaintFlow> taintFlows = collectTaintFlows();
        solver.getResult().storeResult(getClass().getName(), taintFlows);
    }

    private Set<TaintFlow> collectTaintFlows() {
        Set<TaintFlow> taintFlows = new TreeSet<>();
        PointerAnalysisResult result = solver.getResult();

        for (Edge<CSCallSite, CSMethod> edge : this.solver.getCallGraph().edges().collect(Collectors.toList())) {
            CSCallSite callSite = edge.getCallSite();
            JMethod callee = edge.getCallee().getMethod();

            Multimap<Integer, CSObj> tmp = HashMultimap.create();
            for (int i = 0; i < callee.getParamCount(); ++i) {
                int finalI = i;
                result.getPointsToSet(this.csManager.getCSVar(callSite.getContext(), callSite.getCallSite().getInvokeExp().getArg(i))).stream()
                        .filter(csObj -> this.manager.isTaint(csObj.getObject()))
                        .forEach(csObj -> tmp.put(finalI, csObj));
            }

            this.config.getSinks().stream()
                    .filter(sink -> sink.method() == callee)
                    .flatMap(sink -> tmp.get(sink.index()).stream().map(csObj -> new TaintFlow(this.manager.getSourceCall(csObj.getObject()), callSite.getCallSite(), sink.index())))
                    .forEach(taintFlows::add);
        }

        return taintFlows;
    }

    public boolean isSource(JMethod m, Type type) {
        return this.config.getSources().contains(new Source(m, type));
    }

    public CSObj makeTaint(Invoke source) {
        return this.csManager.getCSObj(this.emptyContext, this.manager.makeTaint(source, source.getLValue().getType()));
    }

    public Boolean isTaint(Obj obj) {
        return this.manager.isTaint(obj);
    }

    public PointsToSet getTaintPointsToSet(PointsToSet pointsToSet) {
        PointsToSet result = PointsToSetFactory.make();
        pointsToSet.objects()
                .filter(csObj -> this.manager.isTaint(csObj.getObject()))
                .forEach(result::addObject);
        return result;
    }

    private Stream<TaintTransfer> getTransfers(JMethod method, Type t) {
        return this.config.getTransfers().stream()
                .filter(taintTransfer -> taintTransfer.method() == method && taintTransfer.type() == t);
    }

    public Stream<Integer> getArgToResultTransfers(JMethod method, Type t) {
        return getTransfers(method, t)
                .filter(taintTransfer -> taintTransfer.to() == TaintTransfer.RESULT && taintTransfer.from() >= 0)
                .map(taintTransfer -> taintTransfer.from());
    }

    public Stream<Integer> getArgToBaseTransfers(JMethod method, Type t) {
        return getTransfers(method, t)
                .filter(taintTransfer -> taintTransfer.to() == TaintTransfer.BASE && taintTransfer.from() >= 0)
                .map(taintTransfer -> taintTransfer.from());
    }

    public Stream<JMethod> getBaseToResultTransfers(JMethod method, Type t) {
        return getTransfers(method, t)
                .filter(taintTransfer -> taintTransfer.to() == TaintTransfer.RESULT && taintTransfer.from() == TaintTransfer.BASE)
                .map(taintTransfer -> taintTransfer.method());
    }
}
