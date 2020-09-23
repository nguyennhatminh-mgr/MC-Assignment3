#MSSV: 1712179
from MCVisitor import MCVisitor
from MCParser import MCParser
from AST import *
from functools import *
class ASTGeneration(MCVisitor):
    # def visitProgram(self,ctx:MCParser.ProgramContext):
    #     return Program([FuncDecl(Id("main"),[],self.visit(ctx.mctype()),Block([self.visit(ctx.body())] if ctx.body() else []))])

    # def visitMctype(self,ctx:MCParser.MctypeContext):
    #     if ctx.INTTYPE():
    #         return IntType
    #     else:
    #         return VoidType

    # def visitBody(self,ctx:MCParser.BodyContext):
    #     return self.visit(ctx.funcall())
  
  	
    # def visitFuncall(self,ctx:MCParser.FuncallContext):
    #     return CallExpr(Id(ctx.ID().getText()),[self.visit(ctx.exp())] if ctx.exp() else [])

    # def visitExp(self,ctx:MCParser.ExpContext):
    #     if (ctx.funcall()):
    #         return self.visit(ctx.funcall())
    #     else:
    #         return IntLiteral(int(ctx.INTLIT().getText()))
    def visitProgram(self,ctx:MCParser.ProgramContext):
        return Program(self.visit(ctx.manydeclarations())) 
        
    def visitManydeclarations(self,ctx:MCParser.ManydeclarationsContext):
        # return [self.visit(x) for x in ctx.declaration()]
        return [item for x in ctx.declaration() for item in self.visit(x)]
        # if ctx.manydeclarations():
        #     return self.visit(ctx.manydeclarations())+self.visit(ctx.declaration())
        # else:
        #     return self.visit(ctx.declaration())

    def visitDeclaration(self,ctx:MCParser.DeclarationContext):
        return self.visit(ctx.var_declaration()) if ctx.var_declaration() else self.visit(ctx.func_declaration())

    #Var declaration
    def visitVar_declaration(self,ctx:MCParser.Var_declarationContext): 
        typeID=self.visit(ctx.primitive_type())
        listID=self.visit(ctx.var_list())
        # a=[]
        # for id_x in listID:
        #     if len(id_x)==1:
        #         a.append(VarDecl(Id(id_x[0]),typeID)) 
        #     else:
        #         a.append(VarDecl(Id(id_x[0]),ArrayType(IntLiteral(int(id_x[1])),typeID)))
        # return a
        # return reduce(lambda x,y: y+x,listID[1:],listID[0])
        # [a.append(VarDecl(Id(id_x[0]),typeID)) if len(id_x)==1 else a.append(VarDecl(Id(id_x[0]),ArrayType(IntLiteral(int(id_x[1])),typeID))) for id_x in listID]
        # return [VarDecl(Id(id_x[0]),typeID) if len(id_x)==1 else VarDecl(Id(id_x[0]),ArrayType(int(id_x[1]),typeID)) for id_x in listID]
        return [VarDecl(id_x[0],typeID) if len(id_x)==1 else VarDecl(id_x[0],ArrayType(int(id_x[1]),typeID)) for id_x in listID]
        # return a

    def visitPrimitive_type(self,ctx:MCParser.Primitive_typeContext):
        return IntType() if ctx.INTTYPE() else FloatType() if ctx.FLOATTYPE() else BoolType() if ctx.BOOLTYPE() else StringType() 
    
    def visitVar_list(self,ctx:MCParser.Var_listContext):
        return [self.visit(var_one) for var_one in ctx.var_one()]

    def visitVar_one(self,ctx:MCParser.Var_oneContext):
        return [ctx.ID().getText()] if ctx.ID() else self.visit(ctx.array_id_var())
    
    def visitArray_id_var(self,ctx:MCParser.Array_id_varContext):
        return [ctx.ID().getText()]+[ctx.INTLIT().getText()]
    
    #Function declaration
    def visitFunc_declaration(self,ctx:MCParser.Func_declarationContext):
        #functype is array of two is element, first element is type, second element is ID 
        functype=self.visit(ctx.func_type())
        listpara=self.visit(ctx.func_list_para()) if ctx.func_list_para() else []
        blockStatement=self.visit(ctx.block_statement())
        return [FuncDecl(functype[1],listpara,functype[0],blockStatement)]
        
    def visitFunc_type(self,ctx:MCParser.Func_typeContext):
        return [VoidType()]+[Id(ctx.ID().getText())] if ctx.VOIDTYPE() else [ArrayPointerType(self.visit(ctx.primitive_type()))] + self.visit(ctx.array_id_func()) if ctx.array_id_func() else [self.visit(ctx.primitive_type())]+[Id(ctx.ID().getText())]
    
    def visitArray_id_func(self,ctx:MCParser.Array_id_funcContext):
        return [Id(ctx.ID().getText())]
    
    def visitFunc_list_para(self,ctx:MCParser.Func_list_paraContext):
        return [self.visit(para_one) for para_one in ctx.func_list_para_one()]
    
    def visitFunc_list_para_one(self,ctx:MCParser.Func_list_para_oneContext):
        return VarDecl(ctx.ID().getText(),ArrayPointerType(self.visit(ctx.primitive_type()))) if ctx.LSB() else VarDecl(ctx.ID().getText(),self.visit(ctx.primitive_type()))

    def visitBlock_statement(self,ctx:MCParser.Block_statementContext):
        return Block([item for item_block in ctx.list_in_block() for item in self.visit(item_block)]) if ctx.list_in_block() else Block([])
        
        # rs=[]
        # for a in ctx.list_in_block():
        #     check=self.visit(a)
        #     if isinstance(check,list):
        #         rs=rs+check
        #     else:
        #         rs.append(check)
        # return Block(rs) if rs else Block([])
        # return Block([self.visit(item_block) for item_block in ctx.list_in_block()]) if ctx.list_in_block() else Block([])
    
    def visitList_in_block(self,ctx:MCParser.List_in_blockContext):
        return self.visit(ctx.var_declaration()) if ctx.var_declaration() else [self.visit(ctx.statement())]

    #Expression
    def visitFuncall(self,ctx:MCParser.FuncallContext):
        lst_exp=self.visit(ctx.list_expression()) if ctx.list_expression() else []
        return CallExpr(Id(ctx.ID().getText()),lst_exp)
    def visitList_expression(self,ctx:MCParser.List_expressionContext):
        return [self.visit(item) for item in ctx.expression()]
    def visitExpression(self,ctx:MCParser.ExpressionContext):
        return BinaryOp(ctx.ASSIGN().getText(),self.visit(ctx.expression1()),self.visit(ctx.expression())) if ctx.ASSIGN() else self.visit(ctx.expression1())
    def visitExpression1(self,ctx:MCParser.Expression1Context):
        return BinaryOp(ctx.OR().getText(),self.visit(ctx.expression1()),self.visit(ctx.expression2())) if ctx.OR() else self.visit(ctx.expression2())
    def visitExpression2(self,ctx:MCParser.Expression2Context):
        return BinaryOp(ctx.AND().getText(),self.visit(ctx.expression2()),self.visit(ctx.expression3())) if ctx.AND() else self.visit(ctx.expression3())
    def visitExpression3(self,ctx:MCParser.Expression3Context):
        if ctx.EQUAL():
            return BinaryOp(ctx.EQUAL().getText(),self.visit(ctx.expression4(0)),self.visit(ctx.expression4(1)))
        elif ctx.NOT_EQUAL():
            return BinaryOp(ctx.NOT_EQUAL().getText(),self.visit(ctx.expression4(0)),self.visit(ctx.expression4(1)))
        else:
            return self.visit(ctx.expression4(0))
    def visitExpression4(self,ctx:MCParser.Expression4Context):
        if ctx.LESS_THAN():
            return BinaryOp(ctx.LESS_THAN().getText(),self.visit(ctx.expression5(0)),self.visit(ctx.expression5(1)))
        elif ctx.LESS_THAN_OR_EQUAL():
            return BinaryOp(ctx.LESS_THAN_OR_EQUAL().getText(),self.visit(ctx.expression5(0)),self.visit(ctx.expression5(1)))
        elif ctx.GREATER_THAN():
            return BinaryOp(ctx.GREATER_THAN().getText(),self.visit(ctx.expression5(0)),self.visit(ctx.expression5(1)))
        elif ctx.GREATER_THAN_OR_EQUAL():
            return BinaryOp(ctx.GREATER_THAN_OR_EQUAL().getText(),self.visit(ctx.expression5(0)),self.visit(ctx.expression5(1)))
        else:
            return self.visit(ctx.expression5(0))
    def visitExpression5(self,ctx:MCParser.Expression5Context):
        if ctx.ADD():
            return BinaryOp(ctx.ADD().getText(),self.visit(ctx.expression5()),self.visit(ctx.expression6()))
        elif ctx.SUB():
            return BinaryOp(ctx.SUB().getText(),self.visit(ctx.expression5()),self.visit(ctx.expression6()))
        else:
            return self.visit(ctx.expression6())
    def visitExpression6(self,ctx:MCParser.Expression6Context):
        if ctx.DIVISION():
            return BinaryOp(ctx.DIVISION().getText(),self.visit(ctx.expression6()),self.visit(ctx.expression7()))
        elif ctx.MULTIPLICATION():
            return BinaryOp(ctx.MULTIPLICATION().getText(),self.visit(ctx.expression6()),self.visit(ctx.expression7()))
        elif ctx.MODULUS():
            return BinaryOp(ctx.MODULUS().getText(),self.visit(ctx.expression6()),self.visit(ctx.expression7()))
        else:
            return self.visit(ctx.expression7())
    def visitExpression7(self,ctx:MCParser.Expression7Context):
        if ctx.SUB():
            return UnaryOp(ctx.SUB().getText(),self.visit(ctx.expression7()))
        elif ctx.NOT():
            return UnaryOp(ctx.NOT().getText(),self.visit(ctx.expression7()))
        else:
            return self.visit(ctx.expression8())
    def visitExpression8(self,ctx:MCParser.Expression8Context):
        if ctx.expression():
            return ArrayCell(self.visit(ctx.expression9()),self.visit(ctx.expression()))
        else:
            return self.visit(ctx.expression9())
    def visitExpression9(self,ctx:MCParser.Expression9Context):
        if ctx.expression():
            return self.visit(ctx.expression())
        else:
            return self.visit(ctx.operand())
    def visitOperand(self,ctx:MCParser.OperandContext):
        if ctx.literals():
            return self.visit(ctx.literals())
        elif ctx.ID():
            return Id(ctx.ID().getText())
        else:
            return self.visit(ctx.funcall())
    def visitLiterals(self,ctx:MCParser.LiteralsContext):
        if ctx.INTLIT():
            return IntLiteral(int(ctx.INTLIT().getText()))
        elif ctx.FLOAT_LITERAL():
            return FloatLiteral(float(ctx.FLOAT_LITERAL().getText()))
        elif ctx.STRING_LIT():
            return StringLiteral(ctx.STRING_LIT().getText())
        else:
            return BooleanLiteral(ctx.BOOLEAN_LIT().getText())

    #Statement
    def visitStatement(self,ctx:MCParser.StatementContext):
        return self.visitChildren(ctx)
    def visitCallstatement(self,ctx:MCParser.CallstatementContext):
        return self.visit(ctx.funcall())
    def visitIfstatement(self,ctx:MCParser.IfstatementContext):

        return If(self.visit(ctx.expression()),self.visit(ctx.statement(0)),self.visit(ctx.statement(1))) if ctx.ELSE() else If(self.visit(ctx.expression()),self.visit(ctx.statement(0)))
    def visitDowhile_statement(self,ctx:MCParser.Dowhile_statementContext):
        lst_statement=[self.visit(item) for item in ctx.statement()]
        return Dowhile(lst_statement,self.visit(ctx.expression()))
    def visitForstatement(self,ctx:MCParser.ForstatementContext):
        return For(self.visit(ctx.expression(0)),self.visit(ctx.expression(1)),self.visit(ctx.expression(2)),self.visit(ctx.statement()))
    def visitBreakstatement(self,ctx:MCParser.BreakstatementContext):
        return Break()
    def visitContinuestatement(self,ctx:MCParser.ContinuestatementContext):
        return Continue()
    def visitReturnstatement(self,ctx:MCParser.ReturnstatementContext):
        return Return(self.visit(ctx.expression())) if ctx.expression() else Return()
    def visitExpressionstatement(self,ctx:MCParser.ExpressionstatementContext):
        return self.visit(ctx.expression())
    
    
