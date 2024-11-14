
willCasesplitNonImplicit : Bool => Bool -> ()
willCasesplitNonImplicit @{a} False = ?willCasesplitNonImplicit_rhs_0
willCasesplitNonImplicit @{a} True = ?willCasesplitNonImplicit_rhs_1

willCasesplitAutoImplicit : Bool => Bool -> ()
willCasesplitAutoImplicit @{False} b = ?willCasesplitAutoImplicit_rhs_0
willCasesplitAutoImplicit @{True} b = ?willCasesplitAutoImplicit_rhs_1

willCasesplitAutoThenNonImplicit : Bool => Bool -> ()
willCasesplitAutoThenNonImplicit @{False} b = ?willCasesplitAutoThenNonImplicit_rhs_0
willCasesplitAutoThenNonImplicit @{True} b = ?willCasesplitAutoThenNonImplicit_rhs_1

