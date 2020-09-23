# Generated from main/mc/parser/MC.g4 by ANTLR 4.7.2
from antlr4 import *
if __name__ is not None and "." in __name__:
    from .MCParser import MCParser
else:
    from MCParser import MCParser

# This class defines a complete generic visitor for a parse tree produced by MCParser.

class MCVisitor(ParseTreeVisitor):

    # Visit a parse tree produced by MCParser#program.
    def visitProgram(self, ctx:MCParser.ProgramContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by MCParser#manydeclarations.
    def visitManydeclarations(self, ctx:MCParser.ManydeclarationsContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by MCParser#declaration.
    def visitDeclaration(self, ctx:MCParser.DeclarationContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by MCParser#var_declaration.
    def visitVar_declaration(self, ctx:MCParser.Var_declarationContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by MCParser#primitive_type.
    def visitPrimitive_type(self, ctx:MCParser.Primitive_typeContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by MCParser#var_one.
    def visitVar_one(self, ctx:MCParser.Var_oneContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by MCParser#array_id_var.
    def visitArray_id_var(self, ctx:MCParser.Array_id_varContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by MCParser#var_list.
    def visitVar_list(self, ctx:MCParser.Var_listContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by MCParser#func_declaration.
    def visitFunc_declaration(self, ctx:MCParser.Func_declarationContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by MCParser#func_type.
    def visitFunc_type(self, ctx:MCParser.Func_typeContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by MCParser#array_id_func.
    def visitArray_id_func(self, ctx:MCParser.Array_id_funcContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by MCParser#func_list_para.
    def visitFunc_list_para(self, ctx:MCParser.Func_list_paraContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by MCParser#func_list_para_one.
    def visitFunc_list_para_one(self, ctx:MCParser.Func_list_para_oneContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by MCParser#block_statement.
    def visitBlock_statement(self, ctx:MCParser.Block_statementContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by MCParser#list_in_block.
    def visitList_in_block(self, ctx:MCParser.List_in_blockContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by MCParser#funcall.
    def visitFuncall(self, ctx:MCParser.FuncallContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by MCParser#list_expression.
    def visitList_expression(self, ctx:MCParser.List_expressionContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by MCParser#literals.
    def visitLiterals(self, ctx:MCParser.LiteralsContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by MCParser#operand.
    def visitOperand(self, ctx:MCParser.OperandContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by MCParser#expression.
    def visitExpression(self, ctx:MCParser.ExpressionContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by MCParser#expression1.
    def visitExpression1(self, ctx:MCParser.Expression1Context):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by MCParser#expression2.
    def visitExpression2(self, ctx:MCParser.Expression2Context):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by MCParser#expression3.
    def visitExpression3(self, ctx:MCParser.Expression3Context):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by MCParser#expression4.
    def visitExpression4(self, ctx:MCParser.Expression4Context):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by MCParser#expression5.
    def visitExpression5(self, ctx:MCParser.Expression5Context):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by MCParser#expression6.
    def visitExpression6(self, ctx:MCParser.Expression6Context):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by MCParser#expression7.
    def visitExpression7(self, ctx:MCParser.Expression7Context):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by MCParser#expression8.
    def visitExpression8(self, ctx:MCParser.Expression8Context):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by MCParser#expression9.
    def visitExpression9(self, ctx:MCParser.Expression9Context):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by MCParser#statement.
    def visitStatement(self, ctx:MCParser.StatementContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by MCParser#callstatement.
    def visitCallstatement(self, ctx:MCParser.CallstatementContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by MCParser#ifstatement.
    def visitIfstatement(self, ctx:MCParser.IfstatementContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by MCParser#dowhile_statement.
    def visitDowhile_statement(self, ctx:MCParser.Dowhile_statementContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by MCParser#forstatement.
    def visitForstatement(self, ctx:MCParser.ForstatementContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by MCParser#breakstatement.
    def visitBreakstatement(self, ctx:MCParser.BreakstatementContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by MCParser#continuestatement.
    def visitContinuestatement(self, ctx:MCParser.ContinuestatementContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by MCParser#returnstatement.
    def visitReturnstatement(self, ctx:MCParser.ReturnstatementContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by MCParser#expressionstatement.
    def visitExpressionstatement(self, ctx:MCParser.ExpressionstatementContext):
        return self.visitChildren(ctx)



del MCParser