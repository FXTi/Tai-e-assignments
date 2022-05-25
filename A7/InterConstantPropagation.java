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

import com.google.common.collect.HashMultimap;
import com.google.common.collect.Multimap;
import pascal.taie.World;
import pascal.taie.analysis.dataflow.analysis.constprop.CPFact;
import pascal.taie.analysis.dataflow.analysis.constprop.ConstantPropagation;
import pascal.taie.analysis.dataflow.analysis.constprop.Value;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.analysis.graph.cfg.CFGBuilder;
import pascal.taie.analysis.graph.icfg.CallEdge;
import pascal.taie.analysis.graph.icfg.CallToReturnEdge;
import pascal.taie.analysis.graph.icfg.NormalEdge;
import pascal.taie.analysis.graph.icfg.ReturnEdge;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.analysis.pta.core.cs.element.InstanceField;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.InstanceFieldAccess;
import pascal.taie.ir.exp.InvokeExp;
import pascal.taie.ir.exp.StaticFieldAccess;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.*;
import pascal.taie.language.classes.JField;
import pascal.taie.language.classes.JMethod;
import pascal.taie.util.collection.MultiMap;

import java.util.stream.Collectors;
import java.util.stream.IntStream;

import static pascal.taie.analysis.dataflow.analysis.constprop.ConstantPropagation.canHoldInt;
import static pascal.taie.analysis.dataflow.analysis.constprop.ConstantPropagation.evaluate;

/**
 * Implementation of interprocedural constant propagation for int values.
 */
public class InterConstantPropagation extends
        AbstractInterDataflowAnalysis<JMethod, Stmt, CPFact> {

    public static final String ID = "inter-constprop";

    private final ConstantPropagation cp;

    private Multimap<Var, StoreField> storeInstanceField = HashMultimap.create();
    private Multimap<JField, StoreField> storeStaticField = HashMultimap.create();
    private Multimap<Var, StoreArray> storeArray = HashMultimap.create();
    private Multimap<Var, LoadField> loadInstanceField = HashMultimap.create();
    private Multimap<JField, LoadField> loadStaticField = HashMultimap.create();
    private Multimap<Var, LoadArray> loadArray = HashMultimap.create();

    public InterConstantPropagation(AnalysisConfig config) {
        super(config);
        cp = new ConstantPropagation(new AnalysisConfig(ConstantPropagation.ID));
    }

    @Override
    protected void initialize() {
        String ptaId = getOptions().getString("pta");
        PointerAnalysisResult pta = World.get().getResult(ptaId);
        // You can do initialization work here
        for (Var var: pta.getVars()) {
            this.storeInstanceField.putAll(var, var.getStoreFields());
            this.storeArray.putAll(var, var.getStoreArrays());
            this.loadInstanceField.putAll(var, var.getLoadFields());
            this.loadArray.putAll(var, var.getLoadArrays());
            for (Var v : pta.getVars()) {
                if (pta.getPointsToSet(var).stream().anyMatch(o -> pta.getPointsToSet(v).contains(o))) {
                    this.storeInstanceField.putAll(var, v.getStoreFields());
                    this.storeArray.putAll(var, v.getStoreArrays());
                    this.loadInstanceField.putAll(var, v.getLoadFields());
                    this.loadArray.putAll(var, v.getLoadArrays());
                }
            }
        }
        pta.getCallGraph().reachableMethods()
                .flatMap(m -> m.getIR().getStmts().stream())
                .filter(stmt -> stmt instanceof StoreField && ((StoreField) stmt).isStatic())
                .map(stmt -> (StoreField) stmt)
                .forEach(storeField -> {
                    this.storeStaticField.put(storeField.getFieldRef().resolve(), storeField);
                });
        pta.getCallGraph().reachableMethods()
                .flatMap(m -> m.getIR().getStmts().stream())
                .filter(stmt -> stmt instanceof LoadField && ((LoadField) stmt).isStatic())
                .map(stmt -> (LoadField) stmt)
                .forEach(loadField -> {
                    this.loadStaticField.put(loadField.getFieldRef().resolve(), loadField);
                });
    }

    @Override
    public boolean isForward() {
        return cp.isForward();
    }

    @Override
    public CPFact newBoundaryFact(Stmt boundary) {
        IR ir = icfg.getContainingMethodOf(boundary).getIR();
        return cp.newBoundaryFact(ir.getResult(CFGBuilder.ID));
    }

    @Override
    public CPFact newInitialFact() {
        return cp.newInitialFact();
    }

    @Override
    public void meetInto(CPFact fact, CPFact target) {
        cp.meetInto(fact, target);
    }

    @Override
    protected boolean transferCallNode(Stmt stmt, CPFact in, CPFact out) {
        boolean result = !in.equals(out);
        out.copyFrom(in);
        return result;
    }

    private boolean isArrayIndexAliased(LoadArray va, StoreArray vb) {
        Value a = this.solver.getOutFact(va).get(va.getArrayAccess().getIndex());
        Value b = this.solver.getOutFact(vb).get(vb.getArrayAccess().getIndex());

        if (a.isNAC() && b.isNAC()) {
            return true;
        }
        if (a.isConstant() && b.isConstant() && a.getConstant() == b.getConstant()) {
            return true;
        }
        if ((a.isConstant() && b.isNAC()) || (a.isNAC() && b.isConstant())) {
            return true;
        }
        return false;
    }

    @Override
    protected boolean transferNonCallNode(Stmt stmt, CPFact in, CPFact out) {
        if (stmt instanceof AssignStmt
                && stmt.getDef().filter(v -> v instanceof Var && canHoldInt((Var) v)).isPresent()) {
            CPFact newOut = in.copy();

            if (stmt instanceof LoadField && ((LoadField) stmt).isStatic()) {
                this.storeStaticField.get(((LoadField) stmt).getFieldAccess().getFieldRef().resolve()).stream()
                        .map(storeField -> this.solver.getOutFact(storeField).get(storeField.getRValue()))
                        .reduce((a, b) -> this.cp.meetValue(a, b))
                        .ifPresent(v -> newOut.update(((LoadField) stmt).getLValue(), v));
            }
            if (stmt instanceof LoadField && !((LoadField) stmt).isStatic()) {
                this.storeInstanceField.get(((InstanceFieldAccess) ((LoadField) stmt).getFieldAccess()).getBase()).stream()
                        .filter(storeFiled -> ((LoadField) stmt).getFieldRef().resolve() == storeFiled.getFieldRef().resolve())
                        .map(storeField -> this.solver.getOutFact(storeField).get(storeField.getRValue()))
                        .reduce((a, b) -> this.cp.meetValue(a, b))
                        .ifPresent(v -> newOut.update(((LoadField) stmt).getLValue(), v));
            }
            if (stmt instanceof LoadArray) {
                this.storeArray.get(((LoadArray) stmt).getArrayAccess().getBase()).stream()
                        .filter(store -> isArrayIndexAliased((LoadArray) stmt, store))
                        .map(store -> this.solver.getOutFact(store).get(store.getRValue()))
                        .reduce((a, b) -> this.cp.meetValue(a, b))
                        .ifPresent(v -> newOut.update(((LoadArray) stmt).getLValue(), v));
            }

            if (stmt instanceof LoadField || stmt instanceof LoadArray) {
                boolean result = !newOut.equals(out);
                out.clear();
                out.copyFrom(newOut);
                return result;
            }
        }

        boolean changed = this.cp.transferNode(stmt, in, out);

        if (changed) {
            if (stmt instanceof StoreField) {
                StoreField storeField = (StoreField) stmt;
                (storeField.isStatic()
                        ? this.loadStaticField.get(storeField.getFieldRef().resolve())
                        : this.loadInstanceField.get(((InstanceFieldAccess) storeField.getFieldAccess()).getBase()))
                        .stream().filter(loadField -> loadField.getFieldRef().resolve() == storeField.getFieldRef().resolve())
                        .forEach(this.solver::workListAdd);
            }
            if (stmt instanceof StoreArray) {
                this.loadArray.get(((StoreArray) stmt).getArrayAccess().getBase()).forEach(this.solver::workListAdd);
            }
        }

        return changed;
    }

    @Override
    protected CPFact transferNormalEdge(NormalEdge<Stmt> edge, CPFact out) {
        return out;
    }

    @Override
    protected CPFact transferCallToReturnEdge(CallToReturnEdge<Stmt> edge, CPFact out) {
        final CPFact result = out.copy();
        if (edge.getSource().getDef().filter(l -> l instanceof Var && canHoldInt((Var) l)).isPresent()) {
            result.update((Var) edge.getSource().getDef().get(), Value.getUndef());
        }
        return result;
    }

    @Override
    protected CPFact transferCallEdge(CallEdge<Stmt> edge, CPFact callSiteOut) {
        final InvokeExp invokeExp = ((Invoke) edge.getSource()).getInvokeExp();
        final CPFact result = new CPFact();
        IntStream.range(0, invokeExp.getArgCount())
                .filter(i -> !callSiteOut.get(invokeExp.getArg(i)).isUndef())
                .forEach(i -> result.update(edge.getCallee().getIR().getParam(i), callSiteOut.get(invokeExp.getArg(i))));
        return result;
    }

    @Override
    protected CPFact transferReturnEdge(ReturnEdge<Stmt> edge, CPFact returnOut) {
        final CPFact result = new CPFact();
        if (edge.getCallSite().getDef().filter(l -> l instanceof Var && canHoldInt((Var) l)).isPresent()) {
            edge.getReturnVars().stream()
                    .filter(v -> !returnOut.get(v).isUndef())
                    .map(v -> returnOut.get(v))
                    .reduce((a, b) -> this.cp.meetValue(a, b))
                    .ifPresent(v -> result.update((Var) edge.getCallSite().getDef().get(), v));
        }
        return result;
    }
}
