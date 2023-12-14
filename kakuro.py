from csp import *
from time import time
from itertools import permutations

kakuro_given = [
    ['*', '*', '*', '*', [4, '']],
    ['*', [6, ''], [4, 4], '0', '0'],
    [['', 12], '0', '0', '0', '0'],
    [['', 5], '0', '0', '*', '*']
]


class Kakuro(cons_satis):

    def __init__(self, puzzle):
        self.puzzle = puzzle
        variables = []
        domains = {}
        neighbors = {}

        for i in range(4):
            for j in range(len(puzzle[i])):
                if puzzle[i][j] == "0":
                    var = "X" + str(i) + "," + str(j)
                    # print(var)
                    variables.append(var)
                    domains[var] = [str(num) for num in range(1, 10)]

                if puzzle[i][j] != '0' and puzzle[i][j] != '*':
                    if puzzle[i][j][0] != "":
                        hidden_var = "C_d" + str(i) + "," + str(j)
                        variables.append(hidden_var)

                        cell_counter = 0
                        for m in range(i + 1, len(puzzle)):
                            if puzzle[m][j] != "0":
                                break

                            neigh = "X" + str(m) + "," + str(j)

                            if hidden_var not in neighbors:
                                neighbors[hidden_var] = []
                            neighbors[hidden_var].append(neigh)

                            if neigh not in neighbors:
                                neighbors[neigh] = []
                            neighbors[neigh].append(hidden_var)

                            cell_counter += 1

                        def generate_combinations(digits, length, current="", index=0):
                            if index == length:
                                return [current]

                            combinations = []
                            for digit in digits:
                                combinations.extend(generate_combinations(digits, length, current + digit, index + 1))

                            return combinations

                        combinations = generate_combinations('123456789', cell_counter)
                        valid_combinations = [comb for comb in combinations if
                                              sum(int(x) for x in comb) == puzzle[i][j][0]]
                        domains[hidden_var] = valid_combinations

                    # Sum of cells right
                    if puzzle[i][j][1] != "":
                        hidden_var = "C_r" + str(i) + "," + str(j)
                        variables.append(hidden_var)

                        cell_counter = 0
                        for k in range(j + 1, len(puzzle[i])):
                            if puzzle[i][k] != "0":
                                break

                            neigh = "X" + str(i) + "," + str(k)

                            if hidden_var not in neighbors:
                                neighbors[hidden_var] = []
                            neighbors[hidden_var].append(neigh)

                            if neigh not in neighbors:
                                neighbors[neigh] = []
                            neighbors[neigh].append(hidden_var)

                            cell_counter += 1

                        perms = list(map("".join, permutations('123456789', cell_counter)))
                        domains[hidden_var] = [perm for perm in perms if
                                               sum(int(x) for x in perm) == puzzle[i][j][1]]

        cons_satis.__init__(self, variables, domains, neighbors, self.kakuro_constraint)

    def kakuro_constraint(self, A, a, B, b):
        if A.startswith("X") and B.startswith("C"):
            X_i, X_j = map(int, A[1:].split(","))
            C_i, C_j = map(int, B[3:].split(","))

            if B[2] == "d":
                ind = X_i - C_i - 1
                hidden_var = "C_d" + str(C_i) + "," + str(C_j)

                if b[ind] == a:
                    return True

            else:  # B[2] == "r":
                ind = X_j - C_j - 1
                hidden_var = "C_r" + str(C_i) + "," + str(C_j)

                if b[ind] == a:
                    return True

        elif A.startswith("C") and B.startswith("X"):
            C_i, C_j = map(int, A[3:].split(","))
            X_i, X_j = map(int, B[1:].split(","))

            if A[2] == "d":
                ind = X_i - C_i - 1
                hidden_var = "C_d" + str(C_i) + "," + str(C_j)

                if a[ind] == b:
                    return True

            else:
                ind = X_j - C_j - 1
                hidden_var = "C_r" + str(C_i) + "," + str(C_j)

                if a[ind] == b:
                    return True

        return False

    def print(self, assignment=None):
        for i in range(len(self.puzzle)):
            line = ""
            for j in range(len(self.puzzle[i])):
                if self.puzzle[i][j] == '*':
                    line += " * \t"
                elif self.puzzle[i][j] == "0":
                    var = "X" + str(i) + "," + str(j)
                    if assignment is not None:
                        if var in assignment:
                            line += " " + assignment[var] + " \t"
                        else:
                            line += "_ \t"
                    else:
                        line += "_ \t"
                else:
                    sum1 = str(self.puzzle[i][j][0]) if self.puzzle[i][j][0] else ""
                    sum2 = str(self.puzzle[i][j][1]) if self.puzzle[i][j][1] else ""
                    line += sum1 + "\\" + sum2 + "\t"
            print(line)
            print()

def backtracking(csp, inference=no_inference, assignment=None):
    if assignment is None:
        assignment = {}

    if len(assignment) == len(csp.variables):
        return assignment

    unassigned_vars = [v for v in csp.variables if v not in assignment]
    var = unassigned_vars[0]
    min_legal_values = num_legal_values(csp, var, assignment)

    for v in unassigned_vars[1:]:
        legal_values = num_legal_values(csp, v, assignment)
        if legal_values < min_legal_values:
            var = v
            min_legal_values = legal_values

    for value in csp.domains[var]:
        if csp.nconflicts(var, value, assignment) == 0:
            csp.assign(var, value, assignment)
            removals = csp.suppose(var, value)

            # Check if inference is successful (e.g., forward checking)
            if inference(csp, var, value, assignment, removals):
                # Recursively call backtracking for the updated assignment
                result = backtracking(csp, inference, assignment)
                if result is not None:
                    return result
            csp.restore(removals)

    csp.unassign(var, assignment)
    return None


def forward_checking(csp, var, value, assignment, removals):
    for B in csp.neighbors[var]:
        if B not in assignment:
            for b in csp.curr_domains[B][:]:
                if not csp.constraints(var, value, B, b):
                    csp.prune(B, b, removals)
            if not csp.curr_domains[B]:
                return False
    return True


Kakuro_problem = Kakuro(kakuro_given)
start_time = time()
assignments = backtracking(Kakuro_problem)
end_time = time()
total_time = end_time - start_time
Kakuro_problem.print(assignments)
print("\tBacktracking")
print("\tSolved in", total_time, "seconds.")
print("\tMade", Kakuro_problem.nassigns, "assignments.\n")

Kakuro_problem = Kakuro(kakuro_given)
start_time = time()
assignments = backtracking(Kakuro_problem, inference=forward_checking)
end_time = time()
total_time = end_time - start_time
Kakuro_problem.print(assignments)
print("\tBacktracking with FC")
print("\tSolved in", total_time, "seconds.")
print("\tMade", Kakuro_problem.nassigns, "assignments.\n")
