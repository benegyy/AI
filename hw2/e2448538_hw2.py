import re


def cartesian_product(lists):
    if not lists:
        return [[]]
    rest_product = cartesian_product(lists[1:])
    return [[item] + rest for item in lists[0] for rest in rest_product]


def match_predicate(predicate, fact):
    predicate_match = re.match(r'([A-Za-z]+)\((.*)\)', predicate)
    fact_match = re.match(r'([A-Za-z]+)\((.*)\)', fact)

    if not predicate_match or not fact_match:
        return None

    predicate_name, predicate_args = predicate_match.groups()
    fact_name, fact_args = fact_match.groups()

    if predicate_name != fact_name:
        return None

    predicate_args = predicate_args.split(',')
    fact_args = fact_args.split(',')

    bindings = {}

    for p_arg, f_arg in zip(predicate_args, fact_args):
        if p_arg[0].islower():  #variable
            bindings[p_arg] = f_arg
        elif p_arg != f_arg:  #doesn't match
            return None

    return bindings


def apply_bindings(predicate, bindings):
    return re.sub(r'\b([a-z]+)\b', lambda m: bindings.get(m.group(1), m.group(0)), predicate)


def forward_chaining(kb, q):
    facts = set()
    rules = []

    predicate_pattern = r'[A-Za-z]+\([A-Za-z0-9,]+\)'

    for item in kb:
        if '<-' in item:
            conclusion, premises = item.split('<-')
            conclusion = conclusion.strip()

            conclusion_match = re.search(predicate_pattern, conclusion)
            if conclusion_match:
                conclusion = conclusion_match.group(0)
            else:
#                print(f"Error: Conclusion '{conclusion}' does not match the predicate.")
                continue

            premises_list = re.findall(predicate_pattern, premises)
            if not premises_list:
#                print(f"Error: Premises '{premises}' do not match the predicate.")
                continue

            rules.append((conclusion, premises_list))
        else:
            facts.add(item.strip())

#    print(f"Initial facts: {facts}")
#    print(f"Rules: {rules}")

    inferred_facts = set()
    inference_sequence = []
    new_inferences = True

    while new_inferences:
        new_inferences = False
#        print("\nChecking for new inferences...")

        for conclusion, premises in rules:
#            print(f"Checking rule: {conclusion} <- {premises}")

            all_bindings = []

            for premise in premises:
                premise_bindings = []
                for fact in facts:
                    result = match_predicate(premise, fact)
                    if result is not None:
                        premise_bindings.append(result)
                all_bindings.append(premise_bindings)

            for combination in cartesian_product(all_bindings):
                merged_bindings = {}
                consistent = True
                for binding in combination:
                    for var, value in binding.items():
                        if var in merged_bindings and merged_bindings[var] != value:
                            consistent = False
                            break
                        merged_bindings[var] = value
                    if not consistent:
                        break

                if consistent:
                    inferred_conclusion = apply_bindings(conclusion, merged_bindings)
                    if inferred_conclusion not in facts:
                        facts.add(inferred_conclusion)
                        if inferred_conclusion not in inferred_facts:
                            inferred_facts.add(inferred_conclusion)
                            inference_sequence.append(inferred_conclusion)
                            new_inferences = True
#                            print(f"Inferred: {inferred_conclusion}")

#        print(f"Current facts: {sorted(facts)}")

        if q in facts:
            print(inference_sequence)
            return

    print("Query cannot be proven.")


def match_fact_to_goal(fact, goal):
    fact_match = re.match(r'([A-Za-z]+)\((.*)\)', fact)
    goal_match = re.match(r'([A-Za-z]+)\((.*)\)', goal)
    if not fact_match or not goal_match:
        return None

    fact_name, fact_args = fact_match.groups()
    goal_name, goal_args = goal_match.groups()

    if fact_name != goal_name:
        return None
    fact_args = fact_args.split(',')
    goal_args = goal_args.split(',')

    #    print(f"Fact arguments: {fact_args}")
    #    print(f"Goal arguments: {goal_args}")

    bindings = {}
    for fact_arg, goal_arg in zip(fact_args, goal_args):
        if goal_arg[0].islower():
            bindings[goal_arg] = fact_arg
        elif goal_arg != fact_arg:
            if goal_arg[0].isupper() and fact_arg != goal_arg:
                continue
            else:
                return None
    return bindings


def apply_bindings2(predicate, bindings):
    for var, val in bindings.items():
        predicate = re.sub(r'\b' + re.escape(var) + r'\b', val, predicate)
    return predicate


def backward_chaining(kb, query):
    facts = set()
    rules = []
    predicate_pattern = r'[A-Za-z]+\([A-Za-z0-9,]+\)'

    for item in kb:
        if '<-' in item:
            conclusion, premises = item.split('<-')
            conclusion = conclusion.strip()
            conclusion_match = re.search(predicate_pattern, conclusion)
            if conclusion_match:
                conclusion = conclusion_match.group(0)
            else:
                continue
            premises_list = re.findall(predicate_pattern, premises)
            if not premises_list:
                continue
            rules.append((conclusion, premises_list))
        else:
            facts.add(item.strip())

    #    print(f"Initial facts: {facts}")
    #    print(f"Rules: {rules}")

    def prove(goal, visited, proof_steps, inferred_facts):
        #        print(f"\nProving: {goal}")
        #        print(f"Current Facts: {facts}")
        #        print(f"Inferred Facts: {inferred_facts}")
        if goal in facts:
            #            print(f"{goal} is already in the knowledge base")
            return True

        if goal in visited:
            #            print(f"Cycle detected for {goal}. Skipping.")
            return False
        visited.add(goal)

        for conclusion, premises in rules:
            bindings = match_fact_to_goal(goal, conclusion)
            if bindings is not None:
                #                print(f"Rule matched: {conclusion} <- {', '.join(premises)} with bindings {bindings}")
                grounded_premises = [apply_bindings2(premise, bindings) for premise in premises]
                grounded_goal = apply_bindings2(conclusion, bindings)
                rule_str = f"{', '.join(grounded_premises)} -> {grounded_goal}"
                fully_grounded_premises = []
                if all(prove(premise, visited, proof_steps, inferred_facts) for premise in grounded_premises):
                    final_bindings = {}
                    for premise in grounded_premises:
                        fact_match = next((fact for fact in facts if match_fact_to_goal(fact, premise)), None)
                        if fact_match:
                            final_bindings.update(match_fact_to_goal(fact_match, premise))
                        fully_grounded_premises.append(apply_bindings2(premise, final_bindings))
                    fully_grounded_goal = apply_bindings2(grounded_goal, final_bindings)
                    facts.add(fully_grounded_goal)
                    inferred_facts.add(fully_grounded_goal)
                    grounded_rule_str = f"{fully_grounded_goal} <- {', '.join(fully_grounded_premises)}"
                    proof_steps.append(grounded_rule_str)
                    #                    print(f"Updated grounded_rule_str: {grounded_rule_str}")

                    #                    print(f"Inferred: {fully_grounded_goal}")
                    #                    print(f"Updated Facts: {facts}")
                    visited.remove(goal)
                    return True

        #                print(f"Failed to prove rule: {rule_str}")

        for fact in facts:
            bindings = match_fact_to_goal(fact, goal)
            if bindings:
                grounded_fact = apply_bindings2(goal, bindings)
                #                print(f"{goal} can be matched with {fact}")
                #                print(f"Grounded fact: {grounded_fact}")
                facts.add(grounded_fact)  # Add grounded fact
                inferred_facts.add(grounded_fact)
                visited.remove(goal)
                return True

        visited.remove(goal)
        return False

    visited = set()
    proof_steps = []
    inferred_facts = set()

    if prove(query, visited, proof_steps, inferred_facts):
        for rule in reversed(proof_steps):
            grounded_rule = rule.strip()
            print(f"'{grounded_rule}'")
    else:
        print("\nQuery cannot be proven.")


'''
# Test examples
forward_chaining(
    [
        "Partner(x,y) <- Loves(x,y), Loves(y,x)",
        "Happy(y) <- Gift(x,z), Partner(x,y)",
        "Loves(Feyza,Can)",
        "Loves(Can,Feyza)",
        "Gift(Can,z)"
    ],
    "Happy(Feyza)"
)
#[’Partner(Can, Feyza)’, ’Partner(Feyza, Can)’, ’Happy(Feyza)’]

forward_chaining(
 ["Q(x) <- P(x)",
  "P(x) <- L(x), M(x)",
  "M(x) <- B(x), L(x)",
 "L(x) <- A(x), P(x)",
  "L(x) <- A(x), B(x)", "A(John)", "B(John)"],
 "Q(John)"
 )
#[’P(John)’, ’M(John)’, ’L(John)’, ’Q(John)’]

forward_chaining(
 ["Q(x) <- P(x)", "P(x) <- L(x), M(x)", "M(x) <- B(x), L(x)",
 "L(x) <- A(x), P(x)", "L(x) <- A(x), B(x)", "A(John)"],
 "Q(John)"
 )
# Query cannot be proven.

forward_chaining(
 ["A(x) <- B(x)", "B(x) <- C(x)", "C(x) <- A(x)", "A(John)"],
 "B(John)"
)
#['A(John)', 'B(John)', 'C(John)']

forward_chaining(
 ["Q(x) <- P(x)", "P(x) <- L(x), M(x)", "L(x) <- A(x), B(x)", "M(x) <- C(x)", "D(John)", "E(John)"],
 "Q(John)"
)
#Query cannot be proven.

forward_chaining(
 ["R(x) <- P(x), Q(x)", "P(x) <- S(x), T(x)", "Q(x) <- U(x), V(x)", "S(x) <- W(x)", "T(x) <- W(x)", "U(x) <- W(x)", "V(x) <- W(x)", "W(Jane)"],
 "R(Jane)"
)
#['W(Jane)', 'S(Jane)', 'T(Jane)', 'P(Jane)', 'U(Jane)', 'V(Jane)', 'Q(Jane)', 'R(Jane)']

forward_chaining(
 ["T(x) <- R(x), S(x)", "R(x) <- P(x)", "S(x) <- Q(x)", "P(John)"],
 "T(John)"
)
#Query cannot be proven.

forward_chaining(
 ["Z(x) <- X(x), Y(x)", "X(x) <- A(x), B(x)", "Y(x) <- C(x), D(x)", "A(x) <- E(x)", "B(x) <- E(x)", "C(x) <- E(x)", "D(x) <- E(x)", "E(Sam)"],
 "Z(Sam)"
)
#['E(Sam)', 'A(Sam)', 'B(Sam)', 'X(Sam)', 'C(Sam)', 'D(Sam)', 'Y(Sam)', 'Z(Sam)']

forward_chaining(
 ["K(x) <- M(x), N(x)", "M(x) <- O(x)", "N(x) <- P(x)", "O(Mike)"],
 "K(Mike)"
)
#Query cannot be proven.

forward_chaining(
 ["F(x) <- G(x)", "G(x) <- H(x)", "H(Alice)"],
 "F(Alice)"
)
#['H(Alice)', 'G(Alice)', 'F(Alice)']

forward_chaining(
 ["L(x) <- M(x)", "M(x) <- N(x)", "N(John)", "O(John)"],
 "L(John)"
)
#['N(John)', 'M(John)', 'L(John)']

forward_chaining(
 ["L(x) <- M(x)", "M(x) <- N(x)", "N(Sara)", "O(John)"],
 "L(John)"
)
#Query cannot be proven.

forward_chaining(
 ["A(x) <- B(x), C(x)", "B(x) <- D(x)", "C(x) <- D(x)", "D(x) <- E(x)", "E(Emma)"],
 "A(Emma)"
)
#['E(Emma)', 'D(Emma)', 'B(Emma)', 'C(Emma)', 'A(Emma)']
'''





'''print("\nExample 1: ")
backward_chaining(
    [
        "Criminal(x) <- American(x), Weapon(y), Sells(x,y,z), Hostile(z)",
        "Weapon(x) <- Missile(x)",
        "Missile(M)",
        "Owns(Nono,M)",
        "Sells(West,x,Nono) <- Owns(Nono,x), Missile(x)",
        "Hostile(x) <- Enemy(x,America)",
        "American(West)",
        "Enemy(Nono,America)"
    ],
    "Criminal(West)"
)
#[
#’Criminal(West) < - American(West), Weapon(y), Sells(West, y, z), Hostile(z)’,
#’Missile(M) < - Weapon(M)’,
#’Owns(Nono, M), Missile(M) < - Sells(West, M, Nono)’,
#’Enemy(Nono, America) < - Hostile(Nono)’]

backward_chaining(
    ["Q(x) <- P(x)", "P(x) <- L(x), M(x)", "M(x) <- B(x), L(x)",
     "L(x) <- A(x), P(x)", "L(x) <- A(x), B(x)", "A(John)"],
    "Q(John)"
)
#Query cannot be proven.

backward_chaining(
    ["Q(x) <- P(x)", "P(x) <- L(x), M(x)", "M(x) <- B(x), L(x)",
     "L(x) <- A(x), P(x)", "L(x) <- A(x), B(x)", "A(John)", "B(John)"],
    "Q(John)"
)
#[
#’L(John), M(John)-> P(John)’,
#’B(John), L(John)-> M(John)’,
#’A(John), B(John)-> L(John)’,
#’P(John)-> Q(John)

backward_chaining(
    ["T(x) <- R(x), S(x)", "R(x) <- P(x)", "S(x) <- Q(x)", "P(Mike)"],
    "T(Mike)"
)
# Query cannot be proven.

backward_chaining(
    ["T(x) <- R(x), S(x)", "R(x) <- P(x)", "S(x) <- Q(x)", "P(Mike)", "Q(Mike)"],
    "T(Mike)"
)
# [
# 'P(Mike) -> R(Mike)',
# 'Q(Mike) -> S(Mike)',
# 'R(Mike), S(Mike) -> T(Mike)'
# ]

backward_chaining(
    ["A(x) <- B(x)", "B(x) <- C(x)", "C(x) <- A(x)", "A(Sara)"],
    "A(Sara)"
)
# Query cannot be proven due to infinite loop.

backward_chaining(
    ["Z(x) <- X(x), Y(x)", "X(x) <- A(x)", "Y(x) <- B(x)", "A(Sam)", "B(Sam)"],
    "Z(Sam)"
)
# [
# 'A(Sam) -> X(Sam)',
# 'B(Sam) -> Y(Sam)',
# 'X(Sam), Y(Sam) -> Z(Sam)'
# ]

backward_chaining(
    ["F(x) <- G(x)", "G(x) <- H(x)", "F(x) <- H(x)", "H(Alice)"],
    "F(Alice)"
)
# [
# 'H(Alice) -> G(Alice)',
# 'G(Alice) -> F(Alice)',
# 'H(Alice) -> F(Alice)'
# ]
'''