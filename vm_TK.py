import os
import re
import tkinter as tk
import random
from tkinter import ttk
from tkinter import filedialog

import sys
sys.dont_write_bytecode = True

import ply.lex as lex #PLYをインストール
import ply.yacc as yacc

pc = 1
alloc_opr = 0
path = 0
if_stack = []
while_stack = []
ope_space = []
pro_stack = []
pc_stack = []
com_stack = [] #0:nop, 1:ipush, 2:load, 3:store, 4:jpc, 5:jmp, 6:op, 7:label, 8:rjmp, 9:rstore, 10:par, 11:alloc, 12:free
ope_stack = []
par_num = 0
first = [1,0,0,0,0,0]
first0 = [1,0,0,0,0,0,0]
printtxt0_list = []

pc_txt = []
inv_stack = [[]]
inv = False
last_time_list = []
ln = 1
speed = 100
stop = 0

sub_win = None
pro_list = [[],[],[],[],[],[]]
pc_list = [[],[],[],[],[],[]]
com_list = [[],[],[],[],[],[]]
op_list = [[],[],[],[],[],[]]
dictvalue = [0,0,0,0,0,0]
calc_list = [[0,0],[0,0],[0,0],[0,0],[0,0],[0,0]]
linenum = 1
lineno_list = [[],[],[],[],[],[]]
gyo_num = 0
gyo_list = []
pctxt_color = 0
add_lineno = 0
lastpc = 0
T_F = [0,0,0,0,0,0]
aT_F = [0,0,0,0,0,0]
nT_F = [0,0,0,0,0,0]
dict = {}

# トークンの定義
tokens = ('IDENT', 'NUMBER', 'DO', 'OD', 'PAR', 'REMOVE', 'SKIP', 'FI', 'IF', 'THEN', 'ELSE', 'NOT', 'VAR', 'WHILE', 'PLUS', 'MINUS', 'TIMES', 'EQL',
'SUB', 'RT', 'PARENLEFT', 'PARENRIGHT', 'LBRACE', 'RBRACE', 'SEMICOLON', 'AND')

# 予約語
reserved = {
    'do': 'DO',
    'od': 'OD',
    'par': 'PAR',
    'remove': 'REMOVE',
    'skip': 'SKIP',
    'fi': 'FI',
    'if': 'IF',
    'then': 'THEN',
    'else': 'ELSE',
    'not': 'NOT',
    'var': 'VAR',
    'while': 'WHILE',
}

# 正規表現
t_PLUS = r'\+'
t_MINUS = '-'
t_TIMES = '\*'
t_EQL = '='
t_SUB = '=='
t_RT = '>'
t_PARENLEFT = '\('
t_PARENRIGHT = '\)'
t_LBRACE = '\{'
t_RBRACE = '\}'
t_SEMICOLON = ';'
t_AND = '\&&'

t_ignore = ' \t'

def t_IDENT(t):
    r'[a-zA-Z][a-zA-Z0-9]*'
    t.type = reserved.get(t.value, 'IDENT')
    return t

def t_NUMBER(t):
    r'[1-9][0-9]*|0'
    try:
        t.value = int(t.value)
    except ValueError:
        print("Line %d: integer value %s is too large" % t.lineno, t.value)
        t.value = 0
    return t

def t_newline(t):
    r'\n+'
    t.lexer.lineno += len(t.value)
    global linenum
    linenum += 1

def t_error(t):
    print("Illegal character", t.value[0])
    t.lexer.skip(1)

# 構文規則

def p_program(p):
    '''
    program : d_part q_part r_part
            | d_part q_part PAR q_part1 r_part
    '''

def p_d_part(p):
    '''
    d_part : d_decl d_part
           |
    '''

def p_d_decl(p):
    '''
    d_decl : VAR IDENT SEMICOLON
    '''
    global alloc_opr
    ope_stack.append(alloc_opr)
    com_stack.append(11)
    command1='alloc'
    execute(path,pc,command1,alloc_opr)
    alloc_opr += 1

def p_r_part(p):
    '''
    r_part : r_decl r_part
           |
    '''

def p_r_decl(p):
    '''
    r_decl : REMOVE IDENT SEMICOLON
    '''
    global alloc_opr, lastpc, path
    com_stack.append(12)
    path = 0
    alloc_opr -= 1
    ope_stack.append(alloc_opr)
    command1=' free'
    lastpc = pc
    execute(path,pc,command1,alloc_opr)

def p_q_part1(p):
    '''
    q_part1 : q_partL q_part q_partR q_part1
            | q_partL q_part q_partR
    '''

def p_q_partL(p):
    '''
    q_partL : LBRACE
    '''
    global path, par_num
    com_stack.append(10)
    path += 1
    command1='  par'
    opr = 0
    ope_stack.append(opr)
    par_num += 1
    execute(path,pc,command1,opr)

def p_q_partR(p):
    '''
    q_partR : RBRACE
    '''
    com_stack.append(10)
    command1='  par'
    opr = 1
    ope_stack.append(opr)
    execute(path,pc,command1,opr)

def p_q_part(p):
    '''
    q_part : s1_part s_part
           | s_part
    '''

def p_s1_part(p):
    '''
    s1_part : s_part SEMICOLON s1_part
            | s_part SEMICOLON
    '''

def p_s_part(p):
    '''
    s_part : while c_part do q_part od
           | store_part
           | IF c_part then q_part else q_part fi
           | SKIP
           |
    '''

def p_while(p):
    '''
    while : WHILE
    '''
    while_stack.append(pc)
    ope_space.append(pc)
    com_stack.append(7)
    command1='label'
    lineno_list[path].append(linenum+1)
    execute0(path,pc,command1)

def p_do(p):
    '''
    do : DO
    '''
    ope_stack.append(pc+2)
    com_stack[len(com_stack):len(com_stack)]=[4, 5, 7]
    command1='  jpc'
    lineno_list[path].append(linenum)
    execute0(path,pc,command1)
    ope_stack.append(-1)
    while_stack.append(pc)
    command1='  jmp'
    lineno_list[path].append(linenum)
    execute0(path,pc,command1)
    ope_space.append(pc)
    command1='label'
    lineno_list[path].append(linenum)
    execute0(path,pc,command1)

def p_od(p):
    '''
    od : OD
    '''
    com_stack[len(com_stack):len(com_stack)]=[5, 7]
    while_stack.append(pc)
    ope_stack.append(-1)
    command1='  jmp'
    lineno_list[path].append(linenum+1)
    execute0(path,pc,command1)
    ope_space.append(pc)
    while_stack.append(pc)
    while_stack.append(0)
    command1='label'
    lineno_list[path].append(linenum+1)
    execute0(path,pc,command1)

def p_then(p):
    '''
    then : THEN
    '''
    ope_stack.append(pc+2)
    com_stack[len(com_stack):len(com_stack)]=[4, 5, 7]
    command1='  jpc'
    lineno_list[path].append(linenum)
    execute0(path,pc,command1)
    ope_stack.append(-2)
    if_stack.append(pc)
    command1='  jmp'
    lineno_list[path].append(linenum)
    execute0(path,pc,command1)
    ope_space.append(pc)
    command1='label'
    lineno_list[path].append(linenum)
    execute0(path,pc,command1)

def p_else(p):
    '''
    else : ELSE
    '''
    com_stack[len(com_stack):len(com_stack)]=[5, 7]
    ope_stack.append(-2)
    if_stack.append(pc)
    command1='  jmp'
    lineno_list[path].append(linenum)
    execute0(path,pc,command1)
    ope_space.append(pc)
    if_stack.append(pc)
    command1='label'
    lineno_list[path].append(linenum)
    execute0(path,pc,command1)

def p_fi(p):
    '''
    fi : FI
    '''
    if_stack.append(pc)
    if_stack.append(0)
    ope_space.append(pc)
    com_stack.append(7)
    command1='label'
    lineno_list[path].append(linenum+1)
    execute0(path,pc,command1)

def p_store_part(p):
    '''
    store_part : IDENT EQL e_part
    '''
    com_stack.append(3)
    id = p[1]
    dictupdate(id,0)
    for (i, k) in enumerate(dict):
        if k == id:
            opr = i
            ope_stack.append(opr)
        else:
            continue
    command1='store'
    execute(path,pc,command1,opr)

def p_e_part(p):
    '''
    e_part : id
           | num
           | PARENLEFT e_part PARENRIGHT
           | minus
           | plus
           | times
    '''

def p_id(p):
    '''
    id : IDENT
    '''
    com_stack.append(2)
    id = p[1]
    a = dict[id]
    for (i, k) in enumerate(dict):
        if k == id:
            opr = i
            ope_stack.append(opr)
        else:
            continue
    command1=' load'
    execute(path,pc,command1,opr)

def p_num(p):
    '''
    num : NUMBER
    '''
    com_stack.append(1)
    opr = p[1]
    ope_stack.append(opr)
    command1='ipush'
    execute(path,pc,command1,opr)

def p_minus(p):
    '''
    minus : e_part MINUS e_part
    '''
    com_stack.append(6)
    opr = 2
    ope_stack.append(opr)
    command1='   op'
    execute(path,pc,command1,opr)

def p_plus(p):
    '''
    plus : e_part PLUS e_part
    '''
    com_stack.append(6)
    opr = 0
    ope_stack.append(opr)
    command1='   op'
    execute(path,pc,command1,opr)

def p_times(p):
    '''
    times : e_part TIMES e_part
    '''
    com_stack.append(6)
    opr = 1
    ope_stack.append(opr)
    command1='   op'
    execute(path,pc,command1,opr)

def p_c_part(p):
    '''
    c_part : b_part
           | c_part and c_part
           | not c_part
           | PARENLEFT c_part PARENRIGHT
    '''

def p_and(p):
    '''
    and : AND
    '''
    global pc
    com_stack.append(6)
    ope_stack.append(5)
    pro_stack.append(path)
    pc_stack.append(pc)
    lineno_list[path].append(linenum+1)
    pc += 1

def p_not(p):
    '''
    not : NOT
    '''
    global pc
    com_stack.append(6)
    ope_stack.append(6)
    pro_stack.append(path)
    pc_stack.append(pc)
    lineno_list[path].append(linenum+1)
    pc += 1

def p_b_part(p):
    '''
    b_part : sub
           | rt
    '''

def p_sub(p):
    '''
    sub : e_part SUB e_part
    '''
    com_stack.append(6)
    opr = 4
    ope_stack.append(opr)
    command1='   op'
    execute(path,pc,command1,opr)

def p_rt(p):
    '''
    rt : e_part RT e_part
    '''
    com_stack.append(6)
    opr = 3
    ope_stack.append(opr)
    command1='   op'
    execute(path,pc,command1,opr)

# 構文解析エラー時
def p_error(p):
    if p:
        print ("Syntax error: %d: %r: %r" % (p.lineno, p.value, p.type))
        exit()
    else:
        print("Syntax error at EOF")

def if_jmp():
    l2 = if_stack
    i = 0
    while l2 != []:
        if l2[i] == 0:
            if l2[i-1] != 0:
                if l2[i-2] != 0:
                    if l2[i-3] != 0:
                        if l2[i-4] != 0:
                            l2.pop(i)
                            a = l2.pop(i-1)
                            b = l2.pop(i-2)
                            c = l2.pop(i-3)
                            d = l2.pop(i-4)
                            ope_stack[c-1]=a
                            ope_stack[d-1]=b
                            i = 0
        else:
            i += 1

def while_jmp():
    l = while_stack
    i = 0
    while l != []:
        if l[i] == 0:
            l.pop(i)
            a = l.pop(i-1)
            b = l.pop(i-2)
            c = l.pop(i-3)
            d = l.pop(i-4)
            ope_stack[c-1]=a
            ope_stack[b-1]=d
            i = 0
        else:
            i += 1

def dictupdate(key ,value):
    d = {key:value}
    dict.update(d)

def execute(path,pc_count,command1,opr):
    global pc, gyo_num
    pro_stack.append(path)
    pc_stack.append(pc)
    if command1 == 'alloc' or command1 == ' free' or command1 == '  par':
        lineno_list[path].append(gyo_list[gyo_num])
        gyo_num += 1
    else:
        lineno_list[path].append(linenum+1)
    pc += 1

def execute0(path,pc_count,command1):
    global pc
    pro_stack.append(path)
    pc_stack.append(pc)
    pc += 1

def seiretu():
    for i in pc_stack:
        k = pro_stack[i-1]
        pro_list[k].append(k)
        pc_list[k].append(pc_stack[i-1])
        com_list[k].append(com_stack[i-1])
        op_list[k].append(ope_stack[i-1])

#条件式を満たすまで実行
def calc(symbols, units):
    while True:
        p = -1
        for i in range(len(symbols)):
            if symbols[i] == '*' or symbols[i] == '/':
                p = i
                break
        if p == -1:
            break

        if symbols[p] == '*':
            units[p] = units[p] * units[p + 1]
        if symbols[p] == '/':
            units[p] = units[p] / units[p + 1]
        del units[p + 1]
        del symbols[p]

    result = units[0]
    for i in range(len(symbols)):
        if symbols[i] == '+':
            result = result + units[i + 1]
        if symbols[i] == '-':
            result = result - units[i + 1]
    return result


def solve(expression):
    units = []
    symbols = []

    num = ''
    for c in expression:
        if c.isdigit():
            num = num + c
        else:
            units.append(int(num))
            num = ''
            symbols.append(c)
    units.append(int(num))
    sol = calc(symbols, units)
    return sol


def TorF(expression):
    solves = []
    operands = []
    and_or = []

    expression = expression.replace(" ", "")
    for k, v in dict.items():
        expression = expression.replace(k, str(v))
    expression = expression.replace("AND", "&")
    expression = expression.replace("OR", "|")
    expression = expression.replace("<=", "#")
    expression = expression.replace(">=", "$")
    expression = expression.replace("!=", "!")

    split_ex = ""
    for c in expression:
        if c == "=":
            operands.append(c)
            solves.append(solve(split_ex))
            split_ex = ""
        elif c == "<":
            operands.append(c)
            solves.append(solve(split_ex))
            split_ex = ""
        elif c == ">":
            operands.append(c)
            solves.append(solve(split_ex))
            split_ex = ""
        elif c == "#":
            operands.append(c)
            solves.append(solve(split_ex))
            split_ex = ""
        elif c == "$":
            operands.append(c)
            solves.append(solve(split_ex))
            split_ex = ""
        elif c == "!":
            operands.append(c)
            solves.append(solve(split_ex))
            split_ex = ""
        elif c == "&":
            operands.append(c)
            solves.append(solve(split_ex))
            split_ex = ""
        elif c == "|":
            operands.append(c)
            solves.append(solve(split_ex))
            split_ex = ""
        else:
            split_ex = split_ex + c
    solves.append(solve(split_ex))

    result = solves[0]
    results = []
    for i,j in enumerate(operands):
        if j == "=":
            results.append(solves[i]==solves[i+1])
        elif j == "<":
            results.append(solves[i]<solves[i+1])
        elif j == ">":
            results.append(solves[i]>solves[i+1])
        elif j == "#":
            results.append(solves[i]<=solves[i+1])
        elif j == "$":
            results.append(solves[i]>=solves[i+1])
        elif j == "!":
            results.append(solves[i]!=solves[i+1])
        elif j == "&" or j == "|":
            and_or.append(j)
    i = 0
    while "&" in and_or:
        if and_or[i] == "&":
            del and_or[i]
            results[i] = results[i] and results[i+1]
            del results[i+1]
        i += 1
    i = 0
    while "|" in and_or:
        if and_or[i] == "|":
            del and_or[i]
            results[i] = results[i] or results[i+1]
            del results[i+1]
        i += 1
    if results != []:
        result = results[0]
    return result

def stop_process():
    global stop
    if stop == 1:
        stop = 2

def back_command_reader(com_num):
    if com_num == 1:
        x = 'nop'
    elif com_num == 2:
        x = 'nop'
    elif com_num == 3:
        x = 'restore'
    elif com_num == 4:
        x = 'label'
    elif com_num == 5:
        x = 'label'
    elif com_num == 6:
        x = 'nop'
    elif com_num == 7:
        x = 'rjmp'
    elif com_num == 10:
        x = 'par'
    elif com_num == 11:
        x = 'free'
    elif com_num == 12:
        x = 'alloc'
    return x

def command_reader(com_num):
    if com_num == 1:
        x = 'ipush'
    elif com_num == 2:
        x = 'load'
    elif com_num == 3:
        x = 'store'
    elif com_num == 4:
        x = 'jpc'
    elif com_num == 5:
        x = 'jmp'
    elif com_num == 6:
        x = 'op'
    elif com_num == 7:
        x = 'label'
    elif com_num == 10:
        x = 'par'
    elif com_num == 11:
        x = 'alloc'
    elif com_num == 12:
        x = 'free'
    return x

class Main:
    def __init__(self):
        self.root = None
        self.txt = None
        self.backtxt = None
        self.pctxt = None
        self.pc0 = None
        self.pc1 = None
        self.pc2 = None
        self.pc3 = None
        self.pc4 = None
        self.pc5 = None
        self.check = None
        self.bln = None
        self.bp1 = None
        self.bp2 = None
        self.bp3 = None
        self.bp4 = None
        self.bp5 = None
        self.ForB = None
        self.redobox = None
        self.slabel = None
        self.speedbox = None
        self.joken = None
        self.canvas1 = None
        self.canvas2 = None
        self.tree = None
        self.tree0 = None
        self.tree1 = None
        self.tree2 = None
        self.tree3 = None
        self.tree4 = None
        self.tree5 = None
        self.treeB = None
        self.tree0B = None
        self.tree1B = None
        self.tree2B = None
        self.tree3B = None
        self.tree4B = None
        self.tree5B = None
        self.table = None

    def start(self):
        self.root_window()
        self.reader_widget() #入力
        self.root.mainloop()

    def f_raise(self):
        global inv
        inv = False
        self.ForB["text"] = "Forward mode"
        self.ForB["fg"] = "black"
        self.tree.tkraise()
        self.tree0.tkraise()
        self.canvas1_draw()
        self.canvas2_draw()
        if par_num > 0:
            self.tree1.tkraise()
        if par_num > 1:
            self.tree2.tkraise()
        if par_num > 2:
            self.tree3.tkraise()
        if par_num > 3:
            self.tree4.tkraise()
        if par_num > 4:
            self.tree5.tkraise()

    def b_raise(self):
        global inv
        inv = True
        self.ForB["text"] = "Backward mode"
        self.ForB["fg"] = "red"
        self.treeB.tkraise()
        self.tree0B.tkraise()
        self.canvas1B_draw()
        self.canvas2B_draw()
        if par_num > 0:
            self.tree1B.tkraise()
        if par_num > 1:
            self.tree2B.tkraise()
        if par_num > 2:
            self.tree3B.tkraise()
        if par_num > 3:
            self.tree4B.tkraise()
        if par_num > 4:
            self.tree5B.tkraise()

    def sub_window(self):
        global sub_win
        sub_win = tk.Toplevel()
        sub_win.geometry("1030x600")
        sub_win.title("並列デバッカ")
        self.table_widget()
        self.txt_widget()
        self.treeBview_widget()
        self.treeB.bind("<<TreeviewSelect>>", self.on_treeB_select)
        self.treeview_widget() #プロセス
        self.tree.bind("<<TreeviewSelect>>", self.on_tree_select)
        self.tree0Bview_widget()
        self.tree0B.bind("<<TreeviewSelect>>", self.on_tree0B_select)
        self.tree0view_widget()
        self.tree0.bind("<<TreeviewSelect>>", self.on_tree0_select)
        self.canvas1_widget() #線を描画
        self.canvas2_widget()
        tk.Button(sub_win, text='Forward', command=lambda: self.f_raise()).place(x=15, y=520)
        tk.Button(sub_win, text='Backward', command=lambda: self.b_raise()).place(x=75, y=520)
        if par_num > 0:
            self.tree1Bview_widget()
            self.tree1B.bind("<<TreeviewSelect>>", self.on_tree1B_select)
            self.tree1view_widget()
            self.tree1.bind("<<TreeviewSelect>>", self.on_tree1_select) #行が選択された時の関数を呼び出すための設定
        if par_num > 1:
            self.tree2Bview_widget()
            self.tree2B.bind("<<TreeviewSelect>>", self.on_tree2B_select)
            self.tree2view_widget()
            self.tree2.bind("<<TreeviewSelect>>", self.on_tree2_select)
        if par_num > 2:
            self.tree3Bview_widget()
            self.tree3B.bind("<<TreeviewSelect>>", self.on_tree3B_select)
            self.tree3view_widget()
            self.tree3.bind("<<TreeviewSelect>>", self.on_tree3_select)
        if par_num > 3:
            self.tree4Bview_widget()
            self.tree4B.bind("<<TreeviewSelect>>", self.on_tree4B_select)
            self.tree4view_widget()
            self.tree4.bind("<<TreeviewSelect>>", self.on_tree4_select)
        if par_num > 4:
            self.tree5Bview_widget()
            self.tree5B.bind("<<TreeviewSelect>>", self.on_tree5B_select)
            self.tree5view_widget()
            self.tree5.bind("<<TreeviewSelect>>", self.on_tree5_select)

    def root_window(self):
        self.root = tk.Tk()
        #画面サイズ
        self.root.geometry('300x100')
        #タイトル
        self.root.title('並列デバッカ')

    def read_file(self, path):
        global pc_txt, linenum

        lexer = lex.lex(debug=0)  # 字句解析器
        yacc.yacc()  # 構文解析器

        # ファイルを開いて
        data = open(path).read()
        pc_txt = open(path).readlines()
        while '\n' in pc_txt: #空の行を削除
            pc_txt.remove('\n')

        lexer.input(data)
        while 1:
            tok = lexer.token()
            if not tok:
                break
            token_val = str(tok.value)
            if token_val == "{" or token_val == "}" or token_val == "var" or token_val == "remove":
                gyo_list.append(int(tok.lineno))
        linenum = 0

        # 解析を実行
        yacc.parse(data, lexer=lexer)

        for i in ope_space:
            ope_stack.insert(i-1, lastpc)

        while_jmp()
        if_jmp()
        seiretu()
        if sub_win == None or not sub_win.winfo_exists():
            self.btn_click_read()

        for i in range(5):
            if pc_list[i+1] != []:
                first[i+1] = pc_list[i+1][0]
                first0[i+1] = pc_list[i+1][0]

    def reader_widget(self):
        #レイアウト
        label1 = tk.Label(text='ファイルを選択')
        label1.place(x=10, y=10)
        textBox1 = tk.Entry(width=27)
        textBox1.place(x=10, y=30)
        tk.Button(text='...', command=lambda:self.set_path(textBox1)).place(x=270,y=33)
        tk.Button(text='Read', command=lambda: self.read_file(textBox1.get())).place(x=10, y=70)

    def txt_widget(self):
        self.txt = tk.Text(sub_win, height=35, width=38)
        self.txt.place(x=15,y=15)
        self.txt.tag_config("red", foreground="red")
        self.txt.tag_config("yellow", background="yellow", font=("bold"))
        self.pctxt = tk.Listbox(sub_win, height=27, width=30, bd=2)
        self.pctxt.place(x=15,y=15)
        for text in pc_txt:
            self.pctxt.insert("end", text)
        self.backtxt = tk.Text(sub_win, height=35, width=38)
        self.backtxt.place(x=15,y=15)
        self.backtxt.insert("end","Process0----")
        for i in range(par_num):
            self.backtxt.insert("end",str(i+1)+"----")
        self.backtxt.insert("end","\n")
        self.txt.tkraise()
        self.ForB = tk.Label(sub_win, text="Forward mode")
        self.ForB.place(x=15,y=550)
        redolab = tk.Label(sub_win,text='--Redo--')
        redolab.place(x=350,y=530)
        self.redobox = tk.Entry(sub_win, width=3)
        self.redobox.place(x=350,y=550)
        tk.Button(sub_win, text='Redo', command=lambda: self.redo()).place(x=390, y=553)
        lab0 = tk.Label(sub_win,text='Process0')
        lab0.place(x=350,y=13)
        self.pc0 = tk.Entry(sub_win, width=3)
        self.pc0.place(x=420,y=10)
        labbreak = tk.Label(sub_win,text='Breakpoint')
        labbreak.place(x=470,y=13)
        self.bln = tk.BooleanVar()
        self.bln.set(False)
        self.check = tk.Checkbutton(sub_win, variable=self.bln)
        self.check.place(x=540,y=13)
        tk.Button(sub_win, text='Run', command=lambda: self.bprun()).place(x=560, y=13)
        tk.Button(sub_win, text='Execution', command=lambda: self.txt.tkraise()).place(x=15, y=485)
        tk.Button(sub_win, text='Last route', command=lambda: self.backtxt.tkraise()).place(x=85, y=485)
        tk.Button(sub_win, text='Program', command=lambda: self.pctxt.tkraise()).place(x=155, y=485)
        labjoken = tk.Label(sub_win,text='条件式')
        labjoken.place(x=800,y=133)
        self.joken = tk.Entry(sub_win, width=12)
        self.joken.place(x=850,y=130)
        tk.Button(sub_win, text='Run', command=lambda: self.jokenbprun()).place(x=970, y=133)
        slabel0 = tk.Label(sub_win, text="--Speed--")
        slabel0.place(x=350,y=435)
        self.slabel = tk.Label(sub_win, text="Speed:100")
        self.slabel.place(x=350,y=455)
        self.speedbox = tk.Entry(sub_win, width=5)
        self.speedbox.place(x=350,y=477)
        tk.Button(sub_win, text='Update', command=lambda: self.speed_change()).place(x=410, y=480)
        tk.Button(sub_win, text='Emergency stop button', font=("Lucida Console","20","normal"), fg="red", command=lambda: stop_process()).place(x=800, y=550)
        if par_num > 0:
            lab1 = tk.Label(sub_win,text='Process1')
            lab1.place(x=350,y=33)
            self.pc1 = tk.Entry(sub_win, width=3)
            self.pc1.place(x=420,y=30)
            self.bp1 = tk.Entry(sub_win, width=3)
            self.bp1.place(x=470,y=30)
        if par_num > 1:
            lab2 = tk.Label(sub_win,text='Process2')
            lab2.place(x=350,y=53)
            self.pc2 = tk.Entry(sub_win, width=3)
            self.pc2.place(x=420,y=50)
            self.bp2 = tk.Entry(sub_win, width=3)
            self.bp2.place(x=470,y=50)
        if par_num > 2:
            lab3 = tk.Label(sub_win,text='Process3')
            lab3.place(x=350,y=73)
            self.pc3 = tk.Entry(sub_win, width=3)
            self.pc3.place(x=420,y=70)
            self.bp3 = tk.Entry(sub_win, width=3)
            self.bp3.place(x=470,y=70)
        if par_num > 3:
            lab4 = tk.Label(sub_win,text='Process4')
            lab4.place(x=350,y=93)
            self.pc4 = tk.Entry(sub_win, width=3)
            self.pc4.place(x=420,y=90)
            self.bp4 = tk.Entry(sub_win, width=3)
            self.bp4.place(x=470,y=90)
        if par_num > 4:
            lab5 = tk.Label(sub_win,text='Process5')
            lab5.place(x=350,y=113)
            self.pc5 = tk.Entry(sub_win, width=3)
            self.pc5.place(x=420,y=110)
            self.bp5 = tk.Entry(sub_win, width=3)
            self.bp5.place(x=470,y=110)

    def table_widget(self):
        self.table = ttk.Treeview(sub_win, height=5)
        self.table["columns"] = (1,2)
        self.table["show"] = "headings"
        self.table.heading(1,text="変数")
        self.table.heading(2,text="値")

        self.table.column(1,width=80)
        self.table.column(2,width=30)

        self.table.place(x=850,y=17)

    def btn_click_read(self):
        global first0, add_lineno

        self.sub_window()

        j = 0
        for i, pc in enumerate(pc_list[0]):
            if pc == j+1:
                c = command_reader(com_list[0][i])
                self.tree.insert("", "end", values=(pc, c, op_list[0][i]),tags=[pc])
                cB = back_command_reader(com_list[0][i])
                op = op_list[0][i]
                if cB == "nop":
                    op = 0
                self.tree0B.insert("", "0", values=(lastpc-pc+1, cB, op),tags=[lastpc-pc+1])
                j = pc
                first0[6] = pc_list[0][pc]
                add_lineno += 1

            else:
                c = command_reader(com_list[0][i])
                self.tree0.insert("", "end", values=(pc, c, op_list[0][i]),tags=[pc])
                cB = back_command_reader(com_list[0][i])
                self.treeB.insert("", "0", values=(lastpc-pc+1, cB, op_list[0][i]),tags=[lastpc-pc+1])
        firstlabel = 0
        for i, pc in enumerate(pc_list[1]):
            c = command_reader(com_list[1][i])
            self.tree1.insert("", "end", values=(pc, c, op_list[1][i]),tags=[pc])
            cB = back_command_reader(com_list[1][i])
            op = op_list[1][i]
            if cB == "rjmp":
                if firstlabel == 0:
                    firstlabel = 1
                    self.tree1B.insert("", "0", values=(lastpc-pc+1, "nop", 0),tags=[lastpc-pc+1])
                    continue
            if cB != "par" and cB != "restore":
                op = 0
            if cB == "par":
                if op == 0:
                    op = 1
                else:
                    op = 0
            self.tree1B.insert("", "0", values=(lastpc-pc+1, cB, op),tags=[lastpc-pc+1])
        firstlabel = 0
        for i, pc in enumerate(pc_list[2]):
            c = command_reader(com_list[2][i])
            self.tree2.insert("", "end", values=(pc, c, op_list[2][i]),tags=[pc])
            cB = back_command_reader(com_list[2][i])
            op = op_list[2][i]
            if cB == "rjmp":
                if firstlabel == 0:
                    firstlabel = 1
                    self.tree2B.insert("", "0", values=(lastpc-pc+1, "nop", 0),tags=[lastpc-pc+1])
                    continue
            if cB != "par" and cB != "restore":
                op = 0
            if cB == "par":
                if op == 0:
                    op = 1
                else:
                    op = 0
            self.tree2B.insert("", "0", values=(lastpc-pc+1, cB, op),tags=[lastpc-pc+1])
        firstlabel = 0
        for i, pc in enumerate(pc_list[3]):
            c = command_reader(com_list[3][i])
            self.tree3.insert("", "end", values=(pc, c, op_list[3][i]),tags=[pc])
            cB = back_command_reader(com_list[3][i])
            op = op_list[3][i]
            if cB == "rjmp":
                if firstlabel == 0:
                    firstlabel = 1
                    self.tree3B.insert("", "0", values=(lastpc-pc+1, "nop", 0),tags=[lastpc-pc+1])
                    continue
            if cB != "par" and cB != "restore":
                op = 0
            if cB == "par":
                if op == 0:
                    op = 1
                else:
                    op = 0
            self.tree3B.insert("", "0", values=(lastpc-pc+1, cB, op),tags=[lastpc-pc+1])
        firstlabel = 0
        for i, pc in enumerate(pc_list[4]):
            c = command_reader(com_list[4][i])
            self.tree4.insert("", "end", values=(pc, c, op_list[4][i]),tags=[pc])
            cB = back_command_reader(com_list[4][i])
            op = op_list[4][i]
            if cB == "rjmp":
                if firstlabel == 0:
                    firstlabel = 1
                    self.tree4B.insert("", "0", values=(lastpc-pc+1, "nop", 0),tags=[lastpc-pc+1])
                    continue
            if cB != "par" and cB != "restore":
                op = 0
            if cB == "par":
                if op == 0:
                    op = 1
                else:
                    op = 0
            self.tree4B.insert("", "0", values=(lastpc-pc+1, cB, op),tags=[lastpc-pc+1])
        firstlabel = 0
        for i, pc in enumerate(pc_list[5]):
            c = command_reader(com_list[5][i])
            self.tree5.insert("", "end", values=(pc, c, op_list[5][i]),tags=[pc])
            cB = back_command_reader(com_list[5][i])
            op = op_list[5][i]
            if cB == "rjmp":
                if firstlabel == 0:
                    firstlabel = 1
                    self.tree5B.insert("", "0", values=(lastpc-pc+1, "nop", 0),tags=[lastpc-pc+1])
                    continue
            if cB != "par" and cB != "restore":
                op = 0
            if cB == "par":
                if op == 0:
                    op = 1
                else:
                    op = 0
            self.tree5B.insert("", "0", values=(lastpc-pc+1, cB, op),tags=[lastpc-pc+1])

    def canvas1_widget(self):
        self.canvas1 = tk.Canvas(sub_win, width='700',height='60')
        self.canvas1.place(x=300,y=160)
        self.canvas1.create_line(350,0,350,30)

        for i in range(par_num):
            a = 350 - 75 * (par_num-1) + i * 150
            self.canvas1.create_line(a,30,a,60)
            self.canvas1.create_line(a-10,50,a,60)
            self.canvas1.create_line(a+10,50,a,60)
            if i == 0:
                a_start = a
            a_end = a
        self.canvas1.create_line(a_start,30,a_end,30)

    def canvas2_widget(self):
        self.canvas2 = tk.Canvas(sub_win, width='700',height='60')
        self.canvas2.place(x=300,y=375)
        self.canvas2.create_line(350,30,350,60)
        self.canvas2.create_line(340,50,350,60)
        self.canvas2.create_line(360,50,350,60)

        for i in range(par_num):
            a = 350 - 75 * (par_num-1) + i * 150
            self.canvas2.create_line(a,0,a,30)
            if i == 0:
                a_start = a
            a_end = a
        self.canvas2.create_line(a_start,30,a_end,30)

    def canvas1_draw(self):
        self.canvas1.delete("all")
        self.canvas1.create_line(350,0,350,30)
        for i in range(par_num):
            a = 350 - 75 * (par_num-1) + i * 150
            self.canvas1.create_line(a,30,a,60)
            self.canvas1.create_line(a-10,50,a,60)
            self.canvas1.create_line(a+10,50,a,60)
            if i == 0:
                a_start = a
            a_end = a
        self.canvas1.create_line(a_start,30,a_end,30)

    def canvas2_draw(self):
        self.canvas2.delete("all")
        self.canvas2.create_line(350,30,350,60)
        self.canvas2.create_line(340,50,350,60)
        self.canvas2.create_line(360,50,350,60)
        for i in range(par_num):
            a = 350 - 75 * (par_num-1) + i * 150
            self.canvas2.create_line(a,0,a,30)
            if i == 0:
                a_start = a
            a_end = a
        self.canvas2.create_line(a_start,30,a_end,30)

    def canvas1B_draw(self):
        self.canvas1.delete("all")
        self.canvas1.create_line(350,5,350,30,fill="red")
        self.canvas1.create_line(350,5,340,15,fill="red")
        self.canvas1.create_line(350,5,360,15,fill="red")
        for i in range(par_num):
            a = 350 - 75 * (par_num-1) + i * 150
            self.canvas1.create_line(a,30,a,60,fill="red")
            if i == 0:
                a_start = a
            a_end = a
        self.canvas1.create_line(a_start,30,a_end,30,fill="red")

    def canvas2B_draw(self):
        self.canvas2.delete("all")
        self.canvas2.create_line(350,30,350,60,fill="red")
        for i in range(par_num):
            a = 350 - 75 * (par_num-1) + i * 150
            self.canvas2.create_line(a,5,a,30,fill="red")
            self.canvas2.create_line(a,5,a-10,15,fill="red")
            self.canvas2.create_line(a,5,a+10,15,fill="red")
            if i == 0:
                a_start = a
            a_end = a
        self.canvas2.create_line(a_start,30,a_end,30,fill="red")

    def set_path(self, entry_field):
        entry_field.delete(0, tk.END)
        abs_path = os.path.abspath(os.path.dirname(__file__))
        file_path = filedialog.askopenfilename(initialdir=abs_path)
        entry_field.insert(tk.END, str(file_path))

    def speed_change(self):
        global speed
        if self.speedbox.get() != "":
            speed = int(self.speedbox.get())
            self.slabel["text"] = "Speed:"+str(speed)

    def treeview_widget(self):
        self.tree = ttk.Treeview(sub_win, height=7)
        self.tree["columns"] = (1,2,3)
        self.tree["show"] = "headings"
        self.tree.heading(1,text="pc")
        self.tree.heading(2,text="com")
        self.tree.heading(3,text="op")

        self.tree.column(1,width=30)
        self.tree.column(2,width=50)
        self.tree.column(3,width=30)

        self.tree.place(x=600,y=10)

    def on_tree_select(self, event):
        global pctxt_color, stop
        for id in self.tree.selection():
            pc = self.tree.set(id)["1"]
            self.pctxt.itemconfigure(pctxt_color, fg="black", bg="white")
            pctxt_color = lineno_list[0][int(id.strip("I"),16)-1]-1
            self.pctxt.itemconfigure(pctxt_color, fg="blue", bg="cyan")
            stop = 0
            self.forward(pc,0)

    def treeBview_widget(self):
        self.treeB = ttk.Treeview(sub_win, height=7)
        self.treeB["columns"] = (1,2,3)
        self.treeB["show"] = "headings"
        self.treeB.heading(1,text="pc")
        self.treeB.heading(2,text="com")
        self.treeB.heading(3,text="op")

        self.treeB.column(1,width=30)
        self.treeB.column(2,width=50)
        self.treeB.column(3,width=30)

        self.treeB.place(x=600,y=10)

    def on_treeB_select(self, event):
        global pctxt_color
        for id in self.treeB.selection():
            pc = self.treeB.set(id)["1"]
            self.pctxt.itemconfigure(pctxt_color, fg="black", bg="white")
            pctxt_color = lineno_list[0][-1*int(pc)]-1
            self.pctxt.itemconfigure(pctxt_color, fg="blue", bg="cyan")
            com = self.treeB.set(id)["2"]
            if com == "restore":
                self.backward(pc)

    def tree0view_widget(self):
        self.tree0 = ttk.Treeview(sub_win, height=7)
        self.tree0["columns"] = (1,2,3)
        self.tree0["show"] = "headings"
        self.tree0.heading(1,text="pc")
        self.tree0.heading(2,text="com")
        self.tree0.heading(3,text="op")

        self.tree0.column(1,width=30)
        self.tree0.column(2,width=50)
        self.tree0.column(3,width=30)

        self.tree0.place(x=600,y=440)

    def on_tree0_select(self, event):
        global pctxt_color
        for id in self.tree0.selection():
            pc = self.tree0.set(id)["1"]
            self.printtxt0(pc)
            self.pctxt.itemconfigure(pctxt_color, fg="black", bg="white")
            pctxt_color = lineno_list[0][add_lineno+int(id.strip("I"),16)-1]-1
            self.pctxt.itemconfigure(pctxt_color, fg="blue", bg="cyan")

    def tree0Bview_widget(self):
        self.tree0B = ttk.Treeview(sub_win, height=7)
        self.tree0B["columns"] = (1,2,3)
        self.tree0B["show"] = "headings"
        self.tree0B.heading(1,text="pc")
        self.tree0B.heading(2,text="com")
        self.tree0B.heading(3,text="op")

        self.tree0B.column(1,width=30)
        self.tree0B.column(2,width=50)
        self.tree0B.column(3,width=30)

        self.tree0B.place(x=600,y=440)

    def on_tree0B_select(self, event):
        global pctxt_color
        for id in self.tree0B.selection():
            pc = self.tree0B.set(id)["1"]
            com = self.tree0B.set(id)["2"]
            if com == "restore":
                self.backward(pc)
            elif int(pc) == lastpc:
                self.backward(pc)
            self.pctxt.itemconfigure(pctxt_color, fg="black", bg="white")
            pctxt_color = lineno_list[0][int(id.strip("I"),16)-1]-1
            self.pctxt.itemconfigure(pctxt_color, fg="blue", bg="cyan")

    def printtxt0(self,pc):
        first[0] = first0[6]
        global inv_stack
        for i in range(int(pc) - first0[6]+1):
            if first[0] in printtxt0_list:
                first[0] += 1
                continue
            command1 = "free"
            j = pc_list[0].index(first[0])
            self.txt.insert("end", "~~~~~~~~~~Process"+str(0)+" execute~~~~~~~~~~\npc = "+str(first[0])+" command = "+command1+" operand = "+str(op_list[0][j])+"\n")
            l = list(dict.values())
            self.txt.insert("end", "executing stack :       "+str(l[:op_list[0][j]])+"\n")
            self.txt.insert("end", "shared variable stack : "+str(l[:op_list[0][j]])+"\n")
            inv_stack.append(lastpc-first[0]+1)
            inv_stack.append(l[:op_list[0][j]])

            #色つけ
            if self.pc0.get() != "":
                z = int(self.pc0.get())
                self.tree.tag_configure(z, background="white", foreground="black")
                self.tree0.tag_configure(z, background="white", foreground="black")
                self.treeB.tag_configure(str(lastpc-z+1), background="white", foreground="black")
                self.tree0B.tag_configure(str(lastpc-z+1), background="white", foreground="black")
            self.pc0.delete(0,tk.END)
            self.pc0.insert(tk.END,first[0])
            #現在のpcの背景を青くする
            self.tree0.tag_configure(first[0], background="cyan", foreground="blue")
            self.treeB.tag_configure(str(lastpc-first[0]+1), background="cyan", foreground="blue")

            printtxt0_list.append(first[0])
            first[0] += 1

    def forward(self, pc, pro):
        global dictvalue, T_F, aT_F, nT_F, first, last_time_list, ln, stop
        last_time_list = []
        ln = 1
        limit = 0
        self.backtxt.delete(2.0,tk.END)
        self.backtxt.insert(tk.END,"\n")
        while int(pc) != first[pro]-1:
            if limit == speed:
                if stop == 0:
                    stop = 1
                elif stop == 2:
                    break
                limit = 0
                self.txt.see("end")
                sub_win.after(1000, self.forward, pc, pro)
                break
            limit += 1
            if not (first[pro] in pc_list[pro]):#存在しないpcを選択できなくする
                break

            j = pc_list[pro].index(first[pro])
            command1 = command_reader(com_list[pro][j])
            self.txt.insert("end", "~~~~~~~~~~Process"+str(pro)+" execute~~~~~~~~~~\npc = "+str(first[pro])+" command = "+command1+" operand = "+str(op_list[pro][j])+"\n")

            x = None

            if com_list[pro][j] == 1:
                dictvalue[pro] = op_list[pro][j]
                calc_list[pro].pop(0)
                calc_list[pro].append(dictvalue[pro])
                x = dictvalue[pro]

            elif com_list[pro][j] == 2:
                dictvalue[pro] = op_list[pro][j]
                calc_list[pro].pop(0)
                for i,k in enumerate(dict):
                    if i == op_list[pro][j]:
                        calc_list[pro].append(dict[k])
                x = op_list[pro][j]

            elif com_list[pro][j] == 3:
                for i,k in enumerate(dict):
                    if i == op_list[pro][j]:
                        dict.update({k:dictvalue[pro]})
                        self.table.insert("", "end", values=(k, dictvalue[pro]))

            elif com_list[pro][j] == 6:
                if op_list[pro][j] == 0:
                    dictvalue[pro] = calc_list[pro][0] + calc_list[pro][1]
                if op_list[pro][j] == 1:
                    dictvalue[pro] = calc_list[pro][0] * calc_list[pro][1]
                if op_list[pro][j] == 2:
                    dictvalue[pro] = calc_list[pro][0] - calc_list[pro][1]
                if op_list[pro][j] == 3:#>
                    if calc_list[pro][0] > calc_list[pro][1]:
                        T_F[pro] = 0
                    else:
                        T_F[pro] = 1
                if op_list[pro][j] == 4:#==
                    if calc_list[pro][0] == calc_list[pro][1]:
                        T_F[pro] = 0
                    else:
                        T_F[pro] = 1
                if op_list[pro][j] == 5:#&&
                    aT_F[pro] = T_F[pro]
                if op_list[pro][j] == 6:#NOT
                    nT_F[pro] = 1

            l = list(dict.values())
            l2 = list(dict.values())
            if com_list[pro][j] == 11:
                l = [0]
                l2 = [0]
                for i in range(op_list[pro][j]):
                    l.append(0)
                    l2.append(0)

            #プロセスごとに現在のpcを記述
            if pro == 0:
                if self.pc0.get() != "":
                    z = int(self.pc0.get())
                    self.tree.tag_configure(z, background="white", foreground="black")
                    self.tree0.tag_configure(z, background="white", foreground="black")
                    self.treeB.tag_configure(str(lastpc-z+1), background="white", foreground="black")
                    self.tree0B.tag_configure(str(lastpc-z+1), background="white", foreground="black")
                self.pc0.delete(0,tk.END)
                self.pc0.insert(tk.END,first[pro])
                #現在のpcの背景を青くする
                self.tree.tag_configure(first[pro], background="cyan", foreground="blue")
                self.tree0B.tag_configure(str(lastpc-first[pro]+1), background="cyan", foreground="blue")
            if pro == 1:
                if self.pc1.get() != "":
                    z = int(self.pc1.get())
                    self.tree1.tag_configure(z, background="white", foreground="black")
                    self.tree1B.tag_configure(str(lastpc-z+1), background="white", foreground="black")
                self.pc1.delete(0,tk.END)
                self.pc1.insert(tk.END,first[pro])
                #現在の位置first[pro]の背景を青くする
                self.tree1.tag_configure(first[pro], background="cyan", foreground="blue")
                self.tree1B.tag_configure(str(lastpc-first[pro]+1), background="cyan", foreground="blue")
            if pro == 2:
                if self.pc2.get() != "":
                    z = int(self.pc2.get())
                    self.tree2.tag_configure(z, background="white", foreground="black")
                    self.tree2B.tag_configure(str(lastpc-z+1), background="white", foreground="black")
                self.pc2.delete(0,tk.END)
                self.pc2.insert(tk.END,first[pro])
                self.tree2.tag_configure(first[pro], background="cyan", foreground="blue")
                self.tree2B.tag_configure(str(lastpc-first[pro]+1), background="cyan", foreground="blue")
            if pro == 3:
                if self.pc3.get() != "":
                    z = int(self.pc3.get())
                    self.tree3.tag_configure(z, background="white", foreground="black")
                    self.tree3B.tag_configure(str(lastpc-z+1), background="white", foreground="black")
                self.pc3.delete(0,tk.END)
                self.pc3.insert(tk.END,first[pro])
                self.tree3.tag_configure(first[pro], background="cyan", foreground="blue")
                self.tree3B.tag_configure(str(lastpc-first[pro]+1), background="cyan", foreground="blue")
            if pro == 4:
                if self.pc4.get() != "":
                    z = int(self.pc4.get())
                    self.tree4.tag_configure(z, background="white", foreground="black")
                    self.tree4B.tag_configure(str(lastpc-z+1), background="white", foreground="black")
                self.pc4.delete(0,tk.END)
                self.pc4.insert(tk.END,first[pro])
                self.tree4.tag_configure(first[pro], background="cyan", foreground="blue")
                self.tree4B.tag_configure(str(lastpc-first[pro]+1), background="cyan", foreground="blue")
            if pro == 5:
                if self.pc5.get() != "":
                    z = int(self.pc5.get())
                    self.tree5.tag_configure(z, background="white", foreground="black")
                    self.tree5B.tag_configure(str(lastpc-z+1), background="white", foreground="black")
                self.pc5.delete(0,tk.END)
                self.pc5.insert(tk.END,first[pro])
                self.tree5.tag_configure(first[pro], background="cyan", foreground="blue")
                self.tree5B.tag_configure(str(lastpc-first[pro]+1), background="cyan", foreground="blue")

            if x != None:
                l2.append(x)
            self.txt.insert("end", "executing stack :       "+str(l2)+"\n")
            self.txt.insert("end", "shared variable stack : "+str(l)+"\n")
            inv_stack.append(lastpc-first[pro]+1)
            inv_stack.append(l)
            first[pro] += 1

            #jump操作
            if com_list[pro][j] == 4:
                y = first[pro]-1
                if nT_F[pro] == 1:
                    if T_F[pro] == 1:
                        first[pro] = op_list[pro][j]
                        if int(pc) == y:
                            break
                        self.forward(first[pro],pro)
                elif T_F[pro] == 0:
                    if aT_F[pro] == 0:
                        first[pro] = op_list[pro][j]
                        if int(pc) == y:
                            break
                        self.forward(first[pro],pro)
                aT_F[pro] = 0
                nT_F[pro] = 0
            elif com_list[pro][j] == 5:
                y = first[pro]-1
                first[pro] = op_list[pro][j]
                if int(pc) == y:
                    break

    def backward(self,pc):
        global ln, printtxt0_list
        inv_stack[0] = []
        printtxt0_list = []
        pro_row = pro_list[0]+pro_list[1]+pro_list[2]+pro_list[3]+pro_list[4]+pro_list[5]
        pc_row = pc_list[0]+pc_list[1]+pc_list[2]+pc_list[3]+pc_list[4]+pc_list[5]
        com_row = com_list[0]
        for i in range(5):
            firstlabel = 0
            c = com_list[i+1]
            for j,k in enumerate(c):
                if k == 7 and firstlabel == 0:
                    c[j] = 1
                    firstlabel = 1
            com_row = com_row + c
        ope_row = op_list[0]+op_list[1]+op_list[2]+op_list[3]+op_list[4]+op_list[5]
        while 1 != len(inv_stack):
            i = inv_stack[-2]
            if i == int(pc):

                if i == lastpc:
                    self.txt.insert("end", "~~~~~~~~~~Process"+str(process)+" execute~~~~~~~~~~\npc = "+str(lastpc)+" command = free operand = "+str(0)+"\n", "red")
                    self.txt.insert("end", "shared variable stack : "+str([])+"\n", "red")
                    self.pc0.delete(0,tk.END)
                    first[0] = 1
                    self.tree.tag_configure(lastpc-int(pc)+1, background="white", foreground="black")
                    self.tree0B.tag_configure(int(pc), background="white", foreground="black")
                    num = inv_stack.pop(-2)
                    l = inv_stack.pop(-2)
                    Str = str(ln)
                    for i in range(5-len(Str)):
                        self.backtxt.insert("2.0", " ")
                    self.backtxt.insert("2.0", Str+": ")
                    self.backtxt.insert("2.7", str(lastpc-num+1)+"\n")
                    last_time_list.extend([0, lastpc-num+1])
                break

            num = inv_stack.pop(-2)
            l = inv_stack.pop(-2)
            for j,k in enumerate(pc_row):
                if num == lastpc-k+1:
                    process = pro_row[j]
                    command = back_command_reader(com_row[j])
                    if com_row[j] == 3:
                        operand = ope_row[j]
                        for i,k in enumerate(dict):
                            if i < len(l):
                                dict.update({k:l[i]})
                        x = self.table.get_children()
                        for i,item in enumerate(x):
                            if len(x) == i+1:
                                self.table.delete(item)
                                break
                    elif com_row[j] > 9:
                        operand = ope_row[j]
                    else:
                        operand = 0

            self.txt.insert("end", "~~~~~~~~~~Process"+str(process)+" execute~~~~~~~~~~\npc = "+str(num)+" command = "+str(command)+" operand = "+str(operand)+"\n", "red")
            self.txt.insert("end", "shared variable stack : "+str(l)+"\n", "red")

            first[process] = lastpc-num+1
            if process == 0:
                Str = str(ln)
                for i in range(5-len(Str)):
                    self.backtxt.insert("2.0", " ")
                self.backtxt.insert("2.0", str(ln)+": ")
                self.backtxt.insert("2.7", str(lastpc-num+1)+"\n")
                last_time_list.extend([0, lastpc-num+1])
                if self.pc0.get() != "":
                    z = int(self.pc0.get())
                    self.tree.tag_configure(z, background="white", foreground="black")
                    self.tree0.tag_configure(z, background="white", foreground="black")
                    self.treeB.tag_configure(lastpc-z+1, background="white", foreground="black")
                    self.tree0B.tag_configure(lastpc-z+1, background="white", foreground="black")
                self.pc0.delete(0,tk.END)
                if not first[process] in first0:
                    self.pc0.insert(tk.END,first[process]-1)
                if int(pc) in inv_stack:
                    self.tree.tag_configure(lastpc-int(pc)+1, background="cyan", foreground="blue")
                    self.tree0B.tag_configure(int(pc), background="cyan", foreground="blue")
            if process == 1:
                Str = str(ln)
                for i in range(5-len(Str)):
                    self.backtxt.insert("2.0", " ")
                self.backtxt.insert("2.0", str(ln)+":      ")
                self.backtxt.insert("2.12", str(lastpc-num+1)+"\n")
                last_time_list.extend([1, lastpc-num+1])
                if self.pc1.get() != "":
                    z = int(self.pc1.get())
                    self.tree1.tag_configure(z, background="white", foreground="black")
                    self.tree1B.tag_configure(lastpc-z+1, background="white", foreground="black")
                self.pc1.delete(0,tk.END)
                if not first[process] in first0:
                    self.pc1.insert(tk.END,first[process]-1)
                if int(pc) in inv_stack:
                    self.tree1.tag_configure(lastpc-int(pc)+1, background="cyan", foreground="blue")
                    self.tree1B.tag_configure(int(pc), background="cyan", foreground="blue")
            if process == 2:
                Str = str(ln)
                for i in range(5-len(Str)):
                    self.backtxt.insert("2.0", " ")
                self.backtxt.insert("2.0", str(ln)+":           ")
                self.backtxt.insert("2.17", str(lastpc-num+1)+"\n")
                last_time_list.extend([2, lastpc-num+1])
                if self.pc2.get() != "":
                    z = int(self.pc2.get())
                    self.tree2.tag_configure(z, background="white", foreground="black")
                    self.tree2B.tag_configure(lastpc-z+1, background="white", foreground="black")
                self.pc2.delete(0,tk.END)
                if not first[process] in first0:
                    self.pc2.insert(tk.END,first[process]-1)
                if int(pc) in inv_stack:
                    self.tree2.tag_configure(lastpc-int(pc)+1, background="cyan", foreground="blue")
                    self.tree2B.tag_configure(int(pc), background="cyan", foreground="blue")
            if process == 3:
                Str = str(ln)
                for i in range(5-len(Str)):
                    self.backtxt.insert("2.0", " ")
                self.backtxt.insert("2.0", str(ln)+":                ")
                self.backtxt.insert("2.22", str(lastpc-num+1)+"\n")
                last_time_list.extend([3, lastpc-num+1])
                if self.pc3.get() != "":
                    z = int(self.pc3.get())
                    self.tree3.tag_configure(z, background="white", foreground="black")
                    self.tree3B.tag_configure(lastpc-z+1, background="white", foreground="black")
                self.pc3.delete(0,tk.END)
                if not first[process] in first0:
                    self.pc3.insert(tk.END,first[process]-1)
                if int(pc) in inv_stack:
                    self.tree3.tag_configure(lastpc-int(pc)+1, background="cyan", foreground="blue")
                    self.tree3B.tag_configure(int(pc), background="cyan", foreground="blue")
            if process == 4:
                Str = str(ln)
                for i in range(5-len(Str)):
                    self.backtxt.insert("2.0", " ")
                self.backtxt.insert("2.0", str(ln)+":                     ")
                self.backtxt.insert("2.27", str(lastpc-num+1)+"\n")
                last_time_list.extend([4, lastpc-num+1])
                if self.pc4.get() != "":
                    z = int(self.pc4.get())
                    self.tree4.tag_configure(z, background="white", foreground="black")
                    self.tree4B.tag_configure(lastpc-z+1, background="white", foreground="black")
                self.pc4.delete(0,tk.END)
                if not first[process] in first0:
                    self.pc4.insert(tk.END,first[process]-1)
                if int(pc) in inv_stack:
                    self.tree4.tag_configure(lastpc-int(pc)+1, background="cyan", foreground="blue")
                    self.tree4B.tag_configure(int(pc), background="cyan", foreground="blue")
            if process == 5:
                Str = str(ln)
                for i in range(5-len(Str)):
                    self.backtxt.insert("2.0", " ")
                self.backtxt.insert("2.0", str(ln)+":                          ")
                self.backtxt.insert("2.32", str(lastpc-num+1)+"\n")
                last_time_list.extend([5, lastpc-num+1])
                if self.pc5.get() != "":
                    z = int(self.pc5.get())
                    self.tree5.tag_configure(z, background="white", foreground="black")
                    self.tree5B.tag_configure(lastpc-z+1, background="white", foreground="black")
                self.pc5.delete(0,tk.END)
                if not first[process] in first0:
                    self.pc5.insert(tk.END,first[process]-1)
                if int(pc) in inv_stack:
                    self.tree5.tag_configure(lastpc-int(pc)+1, background="cyan", foreground="blue")
                    self.tree5B.tag_configure(int(pc), background="cyan", foreground="blue")
            ln += 1

    def breakpoint(self,pc,pro):
        if pro == 1:
            if self.bp1.get() != "":
                z = int(self.bp1.get())
                if self.pc1.get() == self.bp1.get():
                    self.tree1.tag_configure(z, background="cyan", foreground="blue")
                    self.tree1B.tag_configure(str(lastpc-z+1), background="cyan", foreground="blue")
                else:
                    self.tree1.tag_configure(z, background="white", foreground="black")
                    self.tree1B.tag_configure(str(lastpc-z+1), background="white", foreground="black")
            self.bp1.delete(0,tk.END)
            self.bp1.insert(tk.END,pc)
            self.tree1.tag_configure(pc, background="white", foreground="red")
            self.tree1B.tag_configure(str(lastpc-int(pc)+1), background="white", foreground="red")
        if pro == 2:
            if self.bp2.get() != "":
                z = int(self.bp2.get())
                if self.pc2.get() == self.bp2.get():
                    self.tree2.tag_configure(z, background="cyan", foreground="blue")
                    self.tree2B.tag_configure(str(lastpc-z+1), background="cyan", foreground="blue")
                else:
                    self.tree2.tag_configure(z, background="white", foreground="black")
                    self.tree2B.tag_configure(str(lastpc-z+1), background="white", foreground="black")
            self.bp2.delete(0,tk.END)
            self.bp2.insert(tk.END,pc)
            self.tree2.tag_configure(pc, background="white", foreground="red")
            self.tree2B.tag_configure(str(lastpc-int(pc)+1), background="white", foreground="red")
        if pro == 3:
            if self.bp3.get() != "":
                z = int(self.bp3.get())
                if self.pc3.get() == self.bp3.get():
                    self.tree3.tag_configure(z, background="cyan", foreground="blue")
                    self.tree3B.tag_configure(str(lastpc-z+1), background="cyan", foreground="blue")
                else:
                    self.tree3.tag_configure(z, background="white", foreground="black")
                    self.tree3B.tag_configure(str(lastpc-z+1), background="white", foreground="black")
            self.bp3.delete(0,tk.END)
            self.bp3.insert(tk.END,pc)
            self.tree3.tag_configure(pc, background="white", foreground="red")
            self.tree3B.tag_configure(str(lastpc-int(pc)+1), background="white", foreground="red")
        if pro == 4:
            if self.bp4.get() != "":
                z = int(self.bp4.get())
                if self.pc4.get() == self.bp4.get():
                    self.tree4.tag_configure(z, background="cyan", foreground="blue")
                    self.tree4B.tag_configure(str(lastpc-z+1), background="cyan", foreground="blue")
                else:
                    self.tree4.tag_configure(z, background="white", foreground="black")
                    self.tree4B.tag_configure(str(lastpc-z+1), background="white", foreground="black")
            self.bp4.delete(0,tk.END)
            self.bp4.insert(tk.END,pc)
            self.tree4.tag_configure(pc, background="white", foreground="red")
            self.tree4B.tag_configure(str(lastpc-int(pc)+1), background="white", foreground="red")
        if pro == 5:
            if self.bp5.get() != "":
                z = int(self.bp5.get())
                if self.pc5.get() == self.bp5.get():
                    self.tree5.tag_configure(z, background="cyan", foreground="blue")
                    self.tree5B.tag_configure(str(lastpc-z+1), background="cyan", foreground="blue")
                else:
                    self.tree5.tag_configure(z, background="white", foreground="black")
                    self.tree5B.tag_configure(str(lastpc-z+1), background="white", foreground="black")
            self.bp5.delete(0,tk.END)
            self.bp5.insert(tk.END,pc)
            self.tree5.tag_configure(pc, background="white", foreground="red")
            self.tree5B.tag_configure(str(lastpc-int(pc)+1), background="white", foreground="red")

    def bprun(self):
        global stop
        bplist = []
        bpnum = [0,0,0,0,0,0]
        if self.bp1 != None and self.bp1.get() != "":
            bpnum[1] = int(self.bp1.get())
            bplist.append(1)
        if self.bp2 != None and self.bp2.get() != "":
            bpnum[2] = int(self.bp2.get())
            bplist.append(2)
        if self.bp3 != None and self.bp3.get() != "":
            bpnum[3] = int(self.bp3.get())
            bplist.append(3)
        if self.bp4 != None and self.bp4.get() != "":
            bpnum[4] = int(self.bp4.get())
            bplist.append(4)
        if self.bp5 != None and self.bp5.get() != "":
            bpnum[5] = int(self.bp5.get())
            bplist.append(5)
        limit = 0
        while bplist != []:
            if limit == speed:
                if stop == 0:
                    stop = 1
                elif stop == 2:
                    break
                limit = 0
                self.txt.see("end")
                sub_win.after(1000, self.bprun)
                break
            limit += 1
            num = random.choice(bplist)
            if not (first[num] in pc_list[num]):
                bplist.remove(num)
                if num == 1:
                    self.bp1.delete(0,tk.END)
                elif num == 2:
                    self.bp2.delete(0,tk.END)
                elif num == 3:
                    self.bp3.delete(0,tk.END)
                elif num == 4:
                    self.bp4.delete(0,tk.END)
                elif num == 5:
                    self.bp5.delete(0,tk.END)
                continue
            self.forward(first[num],num)
            if first[num] == bpnum[num]:
                self.forward(first[num],num)
                bplist.remove(num)
            if bplist == []:
                stop = 0

    def jokenbprun(self):
        global stop
        bplist = []
        inv_list = []
        stop = 0
        for i in range(par_num):
            bplist.append(i+1)
        if self.joken.get() != "":
            joken = TorF(self.joken.get())

            if inv == True:
                list = inv_stack[1::2]
                list.reverse()
                for i in list:
                    if com_stack[-1*i] == 3:
                        inv_list.append(i)
                    elif i == lastpc:
                        inv_list.append(i)
                for i in inv_list:
                    if joken == True:
                        break
                    self.backward(i)
                    joken = TorF(self.joken.get())
            else:
                limit = 0
                while bplist != []:
                    if limit == speed:
                        if stop == 0:
                            stop = 1
                        elif stop == 2:
                            break
                        limit = 0
                        self.txt.see("end")
                        sub_win.after(1000, self.jokenbprun)
                        break
                    limit += 1
                    num = random.choice(bplist)
                    if not (first[num] in pc_list[num]):
                        bplist.remove(num)
                        continue
                    if joken == True:
                        stop = 0
                        break
                    self.forward(first[num],num)
                    joken = TorF(self.joken.get())
                    if bplist == []:
                        stop = 0

    def redo(self):
        ltl = last_time_list
        if self.redobox.get() != "":
            num = int(self.redobox.get())
            while ltl != []:
                if 2*num > len(ltl) or num < 1:
                    break
                pc = ltl.pop()
                pro = ltl.pop()
                self.forward(pc,pro)


    def tree1view_widget(self):
        self.tree1 = ttk.Treeview(sub_win, height=7)
        self.tree1["columns"] = (1,2,3)
        self.tree1["show"] = "headings"
        self.tree1.heading(1,text="pc")
        self.tree1.heading(2,text="com")
        self.tree1.heading(3,text="op")

        self.tree1.column(1,width=30)
        self.tree1.column(2,width=50)
        self.tree1.column(3,width=30)
        a = 600 - 150 * (par_num-1) / 2
        self.tree1.place(x=a,y=225)

    def on_tree1_select(self, event):
        global pctxt_color, stop
        for id in self.tree1.selection():
            pc = self.tree1.set(id)["1"]
            self.pctxt.itemconfigure(pctxt_color, fg="black", bg="white")
            pctxt_color = lineno_list[1][int(id.strip("I"),16)-1]-1
            self.pctxt.itemconfigure(pctxt_color, fg="blue", bg="cyan")
            if self.bln.get():
                self.breakpoint(pc,1)
            else:
                stop = 0
                self.forward(pc,1)

    def tree1Bview_widget(self):
        self.tree1B = ttk.Treeview(sub_win, height=7)
        self.tree1B["columns"] = (1,2,3)
        self.tree1B["show"] = "headings"
        self.tree1B.heading(1,text="pc")
        self.tree1B.heading(2,text="com")
        self.tree1B.heading(3,text="op")

        self.tree1B.column(1,width=30)
        self.tree1B.column(2,width=50)
        self.tree1B.column(3,width=30)
        a = 600 - 150 * (par_num-1) / 2
        self.tree1B.place(x=a,y=225)

    def on_tree1B_select(self, event):
        global pctxt_color
        for id in self.tree1B.selection():
            pc = self.tree1B.set(id)["1"]
            com = self.tree1B.set(id)["2"]
            if com == "restore":
                self.backward(pc)
            self.pctxt.itemconfigure(pctxt_color, fg="black", bg="white")
            pctxt_color = lineno_list[1][int(id.strip("I"),16)-1]-1
            self.pctxt.itemconfigure(pctxt_color, fg="blue", bg="cyan")

    def tree2view_widget(self):
        self.tree2 = ttk.Treeview(sub_win, height=7)
        self.tree2["columns"] = (1,2,3)
        self.tree2["show"] = "headings"
        self.tree2.heading(1,text="pc")
        self.tree2.heading(2,text="com")
        self.tree2.heading(3,text="op")

        self.tree2.column(1,width=30)
        self.tree2.column(2,width=50)
        self.tree2.column(3,width=30)
        a = 750 - 150 * (par_num-1) / 2
        self.tree2.place(x=a,y=225)

    def on_tree2_select(self, event):
        global pctxt_color, stop
        for id in self.tree2.selection():
            pc = self.tree2.set(id)["1"]
            self.pctxt.itemconfigure(pctxt_color, fg="black", bg="white")
            pctxt_color = lineno_list[2][int(id.strip("I"),16)-1]-1
            self.pctxt.itemconfigure(pctxt_color, fg="blue", bg="cyan")
            if self.bln.get():
                self.breakpoint(pc,2)
            else:
                stop = 0
                self.forward(pc,2)

    def tree2Bview_widget(self):
        self.tree2B = ttk.Treeview(sub_win, height=7)
        self.tree2B["columns"] = (1,2,3)
        self.tree2B["show"] = "headings"
        self.tree2B.heading(1,text="pc")
        self.tree2B.heading(2,text="com")
        self.tree2B.heading(3,text="op")

        self.tree2B.column(1,width=30)
        self.tree2B.column(2,width=50)
        self.tree2B.column(3,width=30)
        a = 750 - 150 * (par_num-1) / 2
        self.tree2B.place(x=a,y=225)

    def on_tree2B_select(self, event):
        global pctxt_color
        for id in self.tree2B.selection():
            pc = self.tree2B.set(id)["1"]
            com = self.tree2B.set(id)["2"]
            if com == "restore":
                self.backward(pc)
            self.pctxt.itemconfigure(pctxt_color, fg="black", bg="white")
            pctxt_color = lineno_list[2][int(id.strip("I"),16)-1]-1
            self.pctxt.itemconfigure(pctxt_color, fg="blue", bg="cyan")

    def tree3view_widget(self):
        self.tree3 = ttk.Treeview(sub_win, height=7)
        self.tree3["columns"] = (1,2,3)
        self.tree3["show"] = "headings"
        self.tree3.heading(1,text="pc")
        self.tree3.heading(2,text="com")
        self.tree3.heading(3,text="op")

        self.tree3.column(1,width=30)
        self.tree3.column(2,width=50)
        self.tree3.column(3,width=30)
        a = 900 - 150 * (par_num-1) / 2
        self.tree3.place(x=a,y=225)

    def on_tree3_select(self, event):
        global pctxt_color, stop
        for id in self.tree3.selection():
            pc = self.tree3.set(id)["1"]
            self.pctxt.itemconfigure(pctxt_color, fg="black", bg="white")
            pctxt_color = lineno_list[3][int(id.strip("I"),16)-1]-1
            self.pctxt.itemconfigure(pctxt_color, fg="blue", bg="cyan")
            if self.bln.get():
                self.breakpoint(pc,3)
            else:
                stop = 0
                self.forward(pc,3)

    def tree3Bview_widget(self):
        self.tree3B = ttk.Treeview(sub_win, height=7)
        self.tree3B["columns"] = (1,2,3)
        self.tree3B["show"] = "headings"
        self.tree3B.heading(1,text="pc")
        self.tree3B.heading(2,text="com")
        self.tree3B.heading(3,text="op")

        self.tree3B.column(1,width=30)
        self.tree3B.column(2,width=50)
        self.tree3B.column(3,width=30)
        a = 900 - 150 * (par_num-1) / 2
        self.tree3B.place(x=a,y=225)

    def on_tree3B_select(self, event):
        global pctxt_color
        for id in self.tree3B.selection():
            pc = self.tree3B.set(id)["1"]
            com = self.tree3B.set(id)["2"]
            if com == "restore":
                self.backward(pc)
            self.pctxt.itemconfigure(pctxt_color, fg="black", bg="white")
            pctxt_color = lineno_list[3][int(id.strip("I"),16)-1]-1
            self.pctxt.itemconfigure(pctxt_color, fg="blue", bg="cyan")

    def tree4view_widget(self):
        self.tree4 = ttk.Treeview(sub_win, height=7)
        self.tree4["columns"] = (1,2,3)
        self.tree4["show"] = "headings"
        self.tree4.heading(1,text="pc")
        self.tree4.heading(2,text="com")
        self.tree4.heading(3,text="op")

        self.tree4.column(1,width=30)
        self.tree4.column(2,width=50)
        self.tree4.column(3,width=30)
        a = 1050 - 150 * (par_num-1) / 2
        self.tree4.place(x=a,y=225)

    def on_tree4_select(self, event):
        global pctxt_color, stop
        for id in self.tree4.selection():
            pc = self.tree4.set(id)["1"]
            self.pctxt.itemconfigure(pctxt_color, fg="black", bg="white")
            pctxt_color = lineno_list[4][int(id.strip("I"),16)-1]-1
            self.pctxt.itemconfigure(pctxt_color, fg="blue", bg="cyan")
            if self.bln.get():
                self.breakpoint(pc,4)
            else:
                stop = 0
                self.forward(pc,4)

    def tree4Bview_widget(self):
        self.tree4B = ttk.Treeview(sub_win, height=7)
        self.tree4B["columns"] = (1,2,3)
        self.tree4B["show"] = "headings"
        self.tree4B.heading(1,text="pc")
        self.tree4B.heading(2,text="com")
        self.tree4B.heading(3,text="op")

        self.tree4B.column(1,width=30)
        self.tree4B.column(2,width=50)
        self.tree4B.column(3,width=30)
        a = 1050 - 150 * (par_num-1) / 2
        self.tree4B.place(x=a,y=225)

    def on_tree4B_select(self, event):
        global pctxt_color
        for id in self.tree4B.selection():
            pc = self.tree4B.set(id)["1"]
            com = self.tree4B.set(id)["2"]
            if com == "restore":
                self.backward(pc)
            self.pctxt.itemconfigure(pctxt_color, fg="black", bg="white")
            pctxt_color = lineno_list[4][int(id.strip("I"),16)-1]-1
            self.pctxt.itemconfigure(pctxt_color, fg="blue", bg="cyan")

    def tree5view_widget(self):
        self.tree5 = ttk.Treeview(sub_win, height=7)
        self.tree5["columns"] = (1,2,3)
        self.tree5["show"] = "headings"
        self.tree5.heading(1,text="pc")
        self.tree5.heading(2,text="com")
        self.tree5.heading(3,text="op")

        self.tree5.column(1,width=30)
        self.tree5.column(2,width=50)
        self.tree5.column(3,width=30)
        a = 1200 - 150 * (par_num-1) / 2
        self.tree5.place(x=a,y=225)

    def on_tree5_select(self, event):
        global pctxt_color, stop
        for id in self.tree5.selection():
            pc = self.tree5.set(id)["1"]
            self.pctxt.itemconfigure(pctxt_color, fg="black", bg="white")
            pctxt_color = lineno_list[5][int(id.strip("I"),16)-1]-1
            self.pctxt.itemconfigure(pctxt_color, fg="blue", bg="cyan")
            if self.bln.get():
                self.breakpoint(pc,5)
            else:
                stop = 0
                self.forward(pc,5)

    def tree5Bview_widget(self):
        self.tree5B = ttk.Treeview(sub_win, height=7)
        self.tree5B["columns"] = (1,2,3)
        self.tree5B["show"] = "headings"
        self.tree5B.heading(1,text="pc")
        self.tree5B.heading(2,text="com")
        self.tree5B.heading(3,text="op")

        self.tree5B.column(1,width=30)
        self.tree5B.column(2,width=50)
        self.tree5B.column(3,width=30)
        a = 1200 - 150 * (par_num-1) / 2
        self.tree5B.place(x=a,y=225)

    def on_tree5B_select(self, event):
        global pctxt_color
        for id in self.tree5B.selection():
            pc = self.tree5B.set(id)["1"]
            com = self.tree5B.set(id)["2"]
            if com == "restore":
                self.backward(pc)
            self.pctxt.itemconfigure(pctxt_color, fg="black", bg="white")
            pctxt_color = lineno_list[5][int(id.strip("I"),16)-1]-1
            self.pctxt.itemconfigure(pctxt_color, fg="blue", bg="cyan")

if __name__ == '__main__':
    main = Main()
    main.start()
