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

package pascal.taie.analysis.dataflow.analysis;

import pascal.taie.Assignment;
import pascal.taie.analysis.MethodAnalysis;
import pascal.taie.analysis.dataflow.analysis.constprop.CPFact;
import pascal.taie.analysis.dataflow.analysis.constprop.ConstantPropagation;
import pascal.taie.analysis.dataflow.analysis.constprop.Value;
import pascal.taie.analysis.dataflow.fact.DataflowResult;
import pascal.taie.analysis.dataflow.fact.SetFact;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.analysis.graph.cfg.CFGBuilder;
import pascal.taie.analysis.graph.cfg.Edge;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.ArithmeticExp;
import pascal.taie.ir.exp.ArrayAccess;
import pascal.taie.ir.exp.CastExp;
import pascal.taie.ir.exp.FieldAccess;
import pascal.taie.ir.exp.NewExp;
import pascal.taie.ir.exp.RValue;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.*;
import pascal.taie.util.collection.Pair;
import soot.dava.toolkits.base.AST.traversals.CopyPropagation;

import java.lang.reflect.Constructor;
import java.util.*;
import java.util.stream.Collectors;

public class DeadCodeDetection extends MethodAnalysis {

    public static final String ID = "deadcode";

    public DeadCodeDetection(AnalysisConfig config) {
        super(config);
    }

    @Override
    public Set<Stmt> analyze(IR ir) {
        // obtain CFG
        CFG<Stmt> cfg = ir.getResult(CFGBuilder.ID);
        // obtain result of constant propagation
        DataflowResult<Stmt, CPFact> constants =
                ir.getResult(ConstantPropagation.ID);
        // obtain result of live variable analysis
        DataflowResult<Stmt, SetFact<Var>> liveVars =
                ir.getResult(LiveVariableAnalysis.ID);
        // keep statements (dead code) sorted in the resulting set
        Set<Stmt> deadCode = new TreeSet<>(Comparator.comparing(Stmt::getIndex));

        Set<Stmt> visited = new HashSet<>();
        Stack<Stmt> todo = new Stack<>() {{ add(cfg.getEntry()); }};
        while (!todo.isEmpty()) {
            Stmt curr = todo.pop();
            if (!visited.add(curr)) {
                continue;
            }

            if (curr instanceof If) {
                final If ifStmt = (If) curr;
                Value v = ConstantPropagation.evaluate(ifStmt.getCondition(), constants.getInFact(ifStmt));
                if (v.isConstant()) {
                    todo.add(cfg.getOutEdgesOf(curr).stream()
                            .filter(edge -> edge.getKind() ==
                                    (v.getConstant() == 1 ? Edge.Kind.IF_TRUE : Edge.Kind.IF_FALSE))
                            .map(edge -> edge.getTarget())
                            .findAny()
                            .get());
                    continue;
                }
            }
            if (curr instanceof SwitchStmt) {
                final SwitchStmt switchStmt = (SwitchStmt) curr;
                Value v = ConstantPropagation.evaluate(switchStmt.getVar(), constants.getInFact(switchStmt));
                if (v.isConstant()) {
                    todo.add(cfg.getOutEdgesOf(curr).stream()
                            .filter(edge -> edge.isSwitchCase() && edge.getCaseValue() == v.getConstant()) // **edge.isSwitchCase()**
                            .map(edge -> edge.getTarget())
                            .findAny()
                            .orElse(switchStmt.getDefaultTarget()));
                    continue;
                }
            }
            if (curr instanceof AssignStmt
                    && ((AssignStmt<?, ?>) curr).getLValue() instanceof Var
                    && !liveVars.getOutFact(curr).contains((Var) ((AssignStmt<?, ?>) curr).getLValue())
                    && hasNoSideEffect(((AssignStmt<?, ?>) curr).getRValue())) {
                deadCode.add(curr);
            }
            cfg.getOutEdgesOf(curr).stream().forEach(edge -> todo.add(edge.getTarget()));
        }
        cfg.getNodes().stream().filter(node -> node != cfg.getExit() && !visited.contains(node)).forEach(deadCode::add);
        //ir.getStmts().stream().filter(stmt -> !visited.contains(stmt)).forEach(deadCode::add);

        return deadCode;
    }

    /**
     * @return true if given RValue has no side effect, otherwise false.
     */
    private static boolean hasNoSideEffect(RValue rvalue) {
        // new expression modifies the heap
        if (rvalue instanceof NewExp ||
                // cast may trigger ClassCastException
                rvalue instanceof CastExp ||
                // static field access may trigger class initialization
                // instance field access may trigger NPE
                rvalue instanceof FieldAccess ||
                // array access may trigger NPE
                rvalue instanceof ArrayAccess) {
            return false;
        }
        if (rvalue instanceof ArithmeticExp) {
            ArithmeticExp.Op op = ((ArithmeticExp) rvalue).getOperator();
            // may trigger DivideByZeroException
            return op != ArithmeticExp.Op.DIV && op != ArithmeticExp.Op.REM;
        }
        return true;
    }
}
