
"""
 * @author nhphung
"""
from AST import * 
from Visitor import *
from Utils import Utils
from StaticError import *
from functools import*

class MType:
    def __init__(self,partype,rettype):
        self.partype = partype
        self.rettype = rettype
    #minh them vo
    def __str__(self):
        return 'MType([' + ','.join(str(x) for x in self.partype) + '],' + str(self.rettype) + ')'

class Symbol:
    def __init__(self,name,mtype,value = None):
        self.name = name
        self.mtype = mtype
        self.value = value
    #minh them vo
    def __str__(self):
        return 'Symbol(' + str(self.name) + ',' + str(self.mtype) + ')'

class StaticChecker(BaseVisitor,Utils):

    global_envi = [
    Symbol("getInt",MType([],IntType())),
    Symbol("putIntLn",MType([IntType()],VoidType())),
    Symbol("putInt",MType([IntType()],VoidType())),
    Symbol("getFloat",MType([],FloatType())),
    Symbol("putFloat",MType([FloatType()],VoidType())),
    Symbol("putFloatLn",MType([FloatType()],VoidType())),
    Symbol("putBool",MType([BoolType()],VoidType())),
    Symbol("putBoolLn",MType([BoolType()],VoidType())),
    Symbol("putString",MType([StringType()],VoidType())),
    Symbol("putStringLn",MType([StringType()],VoidType())),
    Symbol("putLn",MType([],VoidType()))
    ]
            
    list_func_check_unreach={}
    
    def __init__(self,ast):
        #print(ast)
        #print(ast)
        #print()
        self.ast = ast


    
    def check(self): 
        return self.visit(self.ast,StaticChecker.global_envi)

    def checkRaiseRedeclare(self,kind,name,list_to_check,func_to_check):
        duplicateName=self.lookup(name,list_to_check,func_to_check)
        if duplicateName is not None:
            raise Redeclared(kind,name)
        return False

    def checkTypeBinary(self,lhs,rhs):
        if type(lhs) is IntType and type(rhs) is IntType:
            return IntType()

    def checkNotLeftValue(self,lhs,list_variable):
        # temp=lhs
        # if type(lhs) is ArrayCell:
        #     if type(lhs.arr) is CallExpr:
        #         temp=lhs.arr.method
        #     else:
        #         temp=lhs.arr
        # if type(temp) is Id:
        #     get_lhs=self.lookup(temp.name,list_variable,lambda x:x.name)
        #     if get_lhs is not None and get_lhs.mtype is not MType:
        #         return True
        if type(lhs) is ArrayCell or type(lhs) is Id:
            return True
        return False
    
    def checkTypeIsCompatible(self,formal_param,actual_param):
        if type(formal_param) is IntType and type(actual_param) is IntType:
            return True
        elif type(formal_param) is FloatType and type(actual_param) in [IntType,FloatType]:
            return True
        elif type(formal_param) is BoolType and type(actual_param) is BoolType:
            return True
        elif type(formal_param) is StringType and type(actual_param) is StringType:
            return True
        elif type(formal_param) is ArrayPointerType and type(actual_param) in [ArrayType,ArrayPointerType]:
            if type(formal_param.eleType) == type(actual_param.eleType):
                return True
        return False

    def visitProgram(self,ast, c): 
        self.list_func_check_unreach={}
        list_global=c.copy()
        for item_decl in ast.decl:
            #variable declaration
            if type(item_decl) is VarDecl:
                self.checkRaiseRedeclare(Variable(),item_decl.variable,list_global,lambda x:x.name)
                list_global.append(Symbol(item_decl.variable,item_decl.varType))
            #function declaration
            else:
                self.checkRaiseRedeclare(Function(),item_decl.name.name,list_global,lambda x:x.name)
                list_global.append(Symbol(item_decl.name.name,MType([item.varType for item in item_decl.param],item_decl.returnType)))
                if item_decl.name.name != "main":
                    self.list_func_check_unreach[item_decl.name.name]=False
        main=self.lookup("main",list_global,lambda x: x.name)
        # if main and type(main.mtype) is MType and type(main.mtype.rettype) is VoidType and len(main.mtype.partype)==0:
        if main and type(main.mtype) is MType:
            [self.visit(x,list_global) for x in ast.decl if type(x) is FuncDecl]
            for key,value in self.list_func_check_unreach.items():
                if value is False:
                    raise UnreachableFunction(key)
            return
        raise NoEntryPoint()

    def visitVarDecl(self,ast,c):
        self.checkRaiseRedeclare(Variable(),ast.variable,c,lambda x:x.name)
        return None
                        

    def visitFuncDecl(self,ast, c): 
        list_local=[]
        #Redeclaration parameter
        for item_param in ast.param:
            self.checkRaiseRedeclare(Parameter(),item_param.variable,list_local,lambda x: x.name)
            list_local.append(Symbol(item_param.variable,item_param.varType))
        list_in_fundecl=[]
        #Retrive item in block
        for item_body_member in ast.body.member:
            if type(item_body_member) is VarDecl:
                self.visit(item_body_member,list_local)
                list_local.append(Symbol(item_body_member.variable,item_body_member.varType))
            #visit other statement
            else:
                temp=self.visit(item_body_member,(c+list_local,self.lookup(ast.name.name,c,lambda x:x.name),False))
                list_in_fundecl.append(temp)

        find_return=self.lookup("return",list_in_fundecl,lambda x:str(x))
        if type(ast.returnType) is not VoidType and find_return is None:
            raise FunctionNotReturn(ast.name.name)
    
    def visitBlock(self,ast,c):
        list_local_in_block=[]
        list_visit=[]
        for mem in ast.member:
            if type(mem) is VarDecl:
                self.visit(mem,list_local_in_block)
                list_local_in_block.append(Symbol(mem.variable,mem.varType))
            else:
                temp=self.visit(mem,(c[0]+list_local_in_block,c[1],c[2]))
                list_visit.append(temp)
        find_return=self.lookup("return",list_visit,lambda x: str(x))
        if find_return is not None:
            return "return"
        return None
        
        
    def visitIf(self,ast,c):
        #TODO
        if_expr=self.visit(ast.expr,c)
        if type(if_expr) is not BoolType:
            raise TypeMismatchInStatement(ast)
        if_thenStmt=self.visit(ast.thenStmt,c)  
        if ast.elseStmt:
            if_elseStmt=self.visit(ast.elseStmt,c)
            if str(if_thenStmt) == "return" and str(if_elseStmt) == "return":
                return "return"
        if str(if_thenStmt)=="return":
            return None
        return None

    def visitFor(self,ast,c):
        for_expr1=self.visit(ast.expr1,c)
        for_expr2=self.visit(ast.expr2,c)
        for_expr3=self.visit(ast.expr3,c)
        for_loop=self.visit(ast.loop,(c[0],c[1],True))
        if type(for_expr1) is not IntType or type(for_expr3) is not IntType or type(for_expr2) is not BoolType:
            raise TypeMismatchInStatement(ast)
        return None

    def visitDowhile(self,ast,c):
        expr_dowhile=self.visit(ast.exp,c)
        if type(expr_dowhile) is not BoolType:
            raise TypeMismatchInStatement(ast)
        list_item_dowhile=[self.visit(x,(c[0],c[1],True)) for x in ast.sl]
        get_return_in_dowhile=self.lookup("return",list_item_dowhile,lambda x: str(x))
        if get_return_in_dowhile is not None:
            return "return"
        return None

    def visitBreak(self,ast,c):
        if not c[2]:
            raise BreakNotInLoop()
        return None

    def visitContinue(self,ast,c):
        if not c[2]:
            raise ContinueNotInLoop()
        return None

    def visitReturn(self,ast,c):
        if type(c[1].mtype.rettype) is not VoidType: #function not return void
            if ast.expr:
                expr_return=self.visit(ast.expr,c)
                #return actual type and return function formal type is not same
                if not self.checkTypeIsCompatible(c[1].mtype.rettype,expr_return):
                    raise TypeMismatchInStatement(ast)
            else: #function but return void type
                raise TypeMismatchInStatement(ast)
            return "return"
        else: #function return void
            if ast.expr:
                raise TypeMismatchInStatement(ast)
        return None

    def visitBinaryOp(self,ast,c):
        operand_left=self.visit(ast.left,c)
        operand_right=self.visit(ast.right,c)
        if ast.op in ["<","<=",">",">="]:
            if type(operand_left) in [IntType,FloatType] and type(operand_right) in [IntType,FloatType]:
                return BoolType()
        elif ast.op in ["==","!="]:
            if (type(operand_left) is IntType and type(operand_right) is IntType) or (type(operand_left) is BoolType and type(operand_right) is BoolType):
                return BoolType()
        elif ast.op in ["+","-","*","/"]:
            if type(operand_left) is IntType and type(operand_right) is IntType:
                return IntType()
            elif type(operand_left) in [IntType,FloatType] and type(operand_right) in [IntType,FloatType]:
                return FloatType()
        elif ast.op == "%":
            if type(operand_left) is IntType and type(operand_right) is IntType:
                return IntType()
        elif ast.op in ["&&","||"]:
            if type(operand_left) is BoolType and type(operand_right) is BoolType:
                return BoolType()
        elif ast.op == "=": 
            if not self.checkNotLeftValue(ast.left,c[0]):
                raise NotLeftValue(ast.left)
            elif type(operand_left) is IntType and type(operand_right) is IntType:
                return IntType()
            elif type(operand_left) is FloatType and type(operand_right) in [IntType,FloatType]:
                return FloatType()
            elif type(operand_left) is BoolType and type(operand_right) is BoolType:
                return BoolType()
            elif type(operand_left) is StringType and type(operand_right) is StringType:
                return StringType()
            
        raise TypeMismatchInExpression(ast) 

    def visitUnaryOp(self,ast,c):
        item_expr=self.visit(ast.body,c)
        if ast.op=="-":
            if type(item_expr) in [IntType,FloatType]:
                return item_expr
        elif ast.op=="!":
            if type(item_expr) is BoolType:
                return BoolType()
        raise TypeMismatchInExpression(ast)

    def visitArrayCell(self,ast,c):
        # if type(ast.arr) is Id:
        #     get_Id=self.lookup(ast.arr.name,c[0][::-1],lambda x: x.name)
        #     if get_Id is None:
        #         raise Undeclared(Identifier(),ast.arr.name)
        #     elif type(get_Id.mtype) is MType:
        #         raise TypeMismatchInExpression(ast)
        item_arr=self.visit(ast.arr,c)
        item_index=self.visit(ast.idx,c)
        if type(item_arr) in [ArrayType,ArrayPointerType] and type(item_index) is IntType:
            return item_arr.eleType
        raise TypeMismatchInExpression(ast)

    def visitId(self,ast,c):
        get_Id=self.lookup(ast.name,c[0][::-1],lambda x: x.name)
        if get_Id is None:
            raise Undeclared(Identifier(),ast.name)
        # elif type(get_Id.mtype) is MType:
        #     raise TypeMismatchInExpression(ast)
        return get_Id.mtype

    def visitCallExpr(self, ast, c): 
        at = [self.visit(x,c) for x in ast.param]
        res = self.lookup(ast.method.name,c[0][::-1],lambda x: x.name)
        if res is None:
            raise Undeclared(Function(),ast.method.name)
        elif type(res.mtype) is not MType:
            raise TypeMismatchInExpression(ast)
        elif len(res.mtype.partype) != len(at):
            raise TypeMismatchInExpression(ast)
        else:
            for item in list(zip(res.mtype.partype,at)):
                if self.checkTypeIsCompatible(item[0],item[1]) == False:
                    raise TypeMismatchInExpression(ast)
        if ast.method.name != c[1].name:
            self.list_func_check_unreach[ast.method.name]=True
        return res.mtype.rettype

    def visitIntLiteral(self,ast, c): 
        return IntType()

    def visitFloatLiteral(self,ast, c): 
        return FloatType()

    def visitStringLiteral(self,ast, c): 
        return StringType()

    def visitBooleanLiteral(self,ast, c): 
        return BoolType()
    

