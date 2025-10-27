import re
import itertools


def remove_implications(expr):
    expr = re.sub(r'\(([^()]*)->([^()]*)\)', r'(¬\1∨\2)', expr)
    return expr.replace('->', '∨')

def move_negations(expr):
    expr = expr.replace('¬(¬', '(')
    expr = expr.replace('¬(∀', '∃¬')
    expr = expr.replace('¬(∃', '∀¬')
    expr = expr.replace('¬(A∧B)', '(¬A∨¬B)')
    expr = expr.replace('¬(A∨B)', '(¬A∧¬B)')
    return expr

def drop_quantifiers(expr):
    return re.sub(r'[∀∃][a-z]\.', '', expr)

def distribute(expr):
    changed = True
    while changed:
        new_expr = re.sub(r'\(([^()]*)∨\(([^()]*)∧([^()]*)\)\)',
                          r'((\1∨\2)∧(\1∨\3))', expr)
        new_expr = re.sub(r'\(\(([^()]*)∧([^()]*)\)∨([^()]*)\)',
                          r'((\1∨\3)∧(\2∨\3))', new_expr)
        changed = new_expr != expr
        expr = new_expr
    return expr

def to_cnf(expr):
    expr = remove_implications(expr)
    expr = move_negations(expr)
    expr = drop_quantifiers(expr)
    expr = distribute(expr)
    return expr


KB = [
    "∀x.(Food(x) -> Likes(John,x))",
    "Food(Apple)",
    "Food(Vegetable)",
    "∀x∀y.((Eats(x,y) ∧ ¬Killed(x)) -> Food(y))",
    "(Eats(Anil,Peanuts) ∧ Alive(Anil))",
    "∀x∀y.(Eats(Anil,y) -> Eats(Harry,y))",
    "∀x.(Alive(x) -> ¬Killed(x))",
    "∀x.(¬Killed(x) -> Alive(x))"
]


goal = "Likes(John,Peanuts)"


print("=== Knowledge Base in CNF ===")
CNF_KB = [to_cnf(s) for s in KB]
for clause in CNF_KB:
    print(clause)


neg_goal = f"¬{goal}"
print("\nNegated Goal (for resolution):", neg_goal)


clauses = set(CNF_KB + [neg_goal])

def resolution(clauses):
    new = set()
    while True:
        pairs = [(c1, c2) for i, c1 in enumerate(clauses)
                 for c2 in list(clauses)[i + 1:]]
        for (ci, cj) in pairs:
            resolvents = resolve(ci, cj)
            if "" in resolvents:
                return True
            new |= set(resolvents)
        if new.issubset(clauses):
            return False
        clauses |= new

def resolve(ci, cj):
    resolvents = set()
    ci_literals = set(ci.replace("(", "").replace(")", "").split("∧"))
    cj_literals = set(cj.replace("(", "").replace(")", "").split("∧"))
    for di in ci_literals:
        for dj in cj_literals:
            if di.strip() == ("¬" + dj.strip()) or dj.strip() == ("¬" + di.strip()):
                new_clause = (ci_literals | cj_literals) - {di, dj}
                resolvents.add("∧".join(new_clause))
    return resolvents

proved = resolution(clauses)
print("\nCan we prove that John likes peanuts?")
print("Result:", "YES (derived contradiction ⇒ proved)" if proved else "NO (cannot prove)")
print("Satish G K 1BM23CS306")
