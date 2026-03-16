#include"BTSolver.hpp"
#include <queue>
#include <unordered_set>

using namespace std;

namespace
{
    enum class ConstraintKind
    {
        Row,
        Col,
        Block,
        Unknown
    };

    int getBoardDimension(ConstraintNetwork& network)
    {
        vector<Constraint> constraints = network.getConstraints();
        if (constraints.empty())
            return 0;
        return constraints[0].size();
    }

    ConstraintKind classifyConstraint(const Constraint& constraint)
    {
        if (constraint.vars.empty())
            return ConstraintKind::Unknown;

        bool sameRow = true;
        bool sameCol = true;
        bool sameBlock = true;

        int row = constraint.vars[0]->row();
        int col = constraint.vars[0]->col();
        int block = constraint.vars[0]->block();

        for (Variable* var : constraint.vars)
        {
            sameRow = sameRow && (var->row() == row);
            sameCol = sameCol && (var->col() == col);
            sameBlock = sameBlock && (var->block() == block);
        }

        if (sameRow)
            return ConstraintKind::Row;
        if (sameCol)
            return ConstraintKind::Col;
        if (sameBlock)
            return ConstraintKind::Block;
        return ConstraintKind::Unknown;
    }

    bool enqueueConstraint(Constraint* constraint, queue<Constraint*>& constraintQueue, unordered_set<Constraint*>& queuedConstraints)
    {
        if (constraint == nullptr)
            return false;
        if (!queuedConstraints.insert(constraint).second)
            return false;
        constraintQueue.push(constraint);
        return true;
    }

    void enqueueRelatedConstraints(ConstraintNetwork& network, Variable* var, queue<Constraint*>& constraintQueue, unordered_set<Constraint*>& queuedConstraints)
    {
        for (Constraint* constraint : network.getConstraintsContainingVariable(var))
            enqueueConstraint(constraint, constraintQueue, queuedConstraints);
    }

    bool enqueueAssignedVariable(Variable* var, queue<Variable*>& assignedQueue, unordered_set<Variable*>& queuedAssigned)
    {
        if (var == nullptr || !var->isAssigned())
            return false;
        if (!queuedAssigned.insert(var).second)
            return false;
        assignedQueue.push(var);
        return true;
    }

    Constraint* findConstraintOfKind(ConstraintNetwork& network, Variable* var, ConstraintKind kind)
    {
        ConstraintNetwork::ConstraintRefSet containingConstraints = network.getConstraintsContainingVariable(var);
        for (Constraint* constraint : containingConstraints)
            if (classifyConstraint(*constraint) == kind)
                return constraint;
        return nullptr;
    }

    // Push variable to trail only if not already pushed in this propagation pass.
    // This avoids redundant domain copies on the trail and speeds up undo.
    void trailPushOnce(Trail* trail, Variable* var, unordered_set<Variable*>& pushed)
    {
        if (pushed.insert(var).second)
            trail->push(var);
    }

    bool assignValueAndEnqueue(ConstraintNetwork& network, Trail* trail, Variable* var, int forcedValue, queue<Variable*>& assignedQueue, unordered_set<Variable*>& queuedAssigned, queue<Constraint*>& constraintQueue, unordered_set<Constraint*>& queuedConstraints, unordered_map<Variable*, int>* assignedMap, unordered_set<Variable*>& pushed)
    {
        if (var->isAssigned())
            return var->getAssignment() == forcedValue;

        trailPushOnce(trail, var, pushed);
        var->assignValue(forcedValue);
        if (assignedMap != nullptr)
            (*assignedMap)[var] = forcedValue;
        enqueueAssignedVariable(var, assignedQueue, queuedAssigned);
        enqueueRelatedConstraints(network, var, constraintQueue, queuedConstraints);
        return true;
    }

    bool enqueueAndAssignSingleton(ConstraintNetwork& network, Variable* var, Trail* trail, queue<Variable*>& assignedQueue, unordered_set<Variable*>& queuedAssigned, queue<Constraint*>& constraintQueue, unordered_set<Constraint*>& queuedConstraints, unordered_map<Variable*, int>* assignedMap, unordered_set<Variable*>& pushed)
    {
        if (var->isAssigned())
            return true;

        Domain domain = var->getDomain();
        if (domain.isEmpty())
            return false;
        if (domain.size() != 1)
            return true;

        int forcedValue = domain.getValues()[0];
        return assignValueAndEnqueue(network, trail, var, forcedValue, assignedQueue, queuedAssigned, constraintQueue, queuedConstraints, assignedMap, pushed);
    }

    bool eliminateValueFromVariable(ConstraintNetwork& network, Trail* trail, Variable* var, int value, queue<Variable*>& assignedQueue, unordered_set<Variable*>& queuedAssigned, queue<Constraint*>& constraintQueue, unordered_set<Constraint*>& queuedConstraints, unordered_map<Variable*, int>* assignedMap, unordered_set<Variable*>& pushed)
    {
        if (var->isAssigned())
            return var->getAssignment() != value;
        if (!var->getDomain().contains(value))
            return true;

        trailPushOnce(trail, var, pushed);
        var->removeValueFromDomain(value);
        enqueueRelatedConstraints(network, var, constraintQueue, queuedConstraints);

        if (var->getDomain().isEmpty())
            return false;

        return enqueueAndAssignSingleton(network, var, trail, assignedQueue, queuedAssigned, constraintQueue, queuedConstraints, assignedMap, pushed);
    }

    bool propagateAssignedValues(ConstraintNetwork& network, Trail* trail, queue<Variable*>& assignedQueue, unordered_set<Variable*>& queuedAssigned, queue<Constraint*>& constraintQueue, unordered_set<Constraint*>& queuedConstraints, unordered_map<Variable*, int>* assignedMap, unordered_set<Variable*>& pushed)
    {
        while (!assignedQueue.empty())
        {
            Variable* assignedVar = assignedQueue.front();
            assignedQueue.pop();
            queuedAssigned.erase(assignedVar);

            if (!assignedVar->isAssigned())
                continue;

            int assignedValue = assignedVar->getAssignment();
            ConstraintNetwork::VariableSet neighbors = network.getNeighborsOfVariable(assignedVar);
            for (Variable* neighbor : neighbors)
            {
                if (!eliminateValueFromVariable(network, trail, neighbor, assignedValue, assignedQueue, queuedAssigned, constraintQueue, queuedConstraints, assignedMap, pushed))
                    return false;
            }
        }
        return true;
    }

    bool applyHiddenSingles(ConstraintNetwork& network, Constraint& constraint, Trail* trail, int N, queue<Variable*>& assignedQueue, unordered_set<Variable*>& queuedAssigned, queue<Constraint*>& constraintQueue, unordered_set<Constraint*>& queuedConstraints, unordered_map<Variable*, int>* assignedMap, unordered_set<Variable*>& pushed)
    {
        unordered_set<int> assignedValues;
        for (Variable* var : constraint.vars)
        {
            if (!var->isAssigned())
                continue;

            int val = var->getAssignment();
            if (assignedValues.count(val) > 0)
                return false;
            assignedValues.insert(val);
        }

        for (int val = 1; val <= N; ++val)
        {
            if (assignedValues.count(val) > 0)
                continue;

            int candidateCount = 0;
            Variable* onlyCandidate = nullptr;
            for (Variable* var : constraint.vars)
            {
                if (var->isAssigned())
                    continue;
                if (!var->getDomain().contains(val))
                    continue;

                candidateCount++;
                onlyCandidate = var;
                if (candidateCount > 1)
                    break;
            }

            if (candidateCount == 0)
                return false;

            if (candidateCount == 1)
            {
                if (!assignValueAndEnqueue(network, trail, onlyCandidate, val, assignedQueue, queuedAssigned, constraintQueue, queuedConstraints, assignedMap, pushed))
                    return false;
            }
        }

        return true;
    }

    bool applyPointingAndClaiming(ConstraintNetwork& network, Constraint& constraint, Trail* trail, int N, queue<Variable*>& assignedQueue, unordered_set<Variable*>& queuedAssigned, queue<Constraint*>& constraintQueue, unordered_set<Constraint*>& queuedConstraints, unordered_map<Variable*, int>* assignedMap, unordered_set<Variable*>& pushed)
    {
        ConstraintKind kind = classifyConstraint(constraint);
        if (kind == ConstraintKind::Unknown)
            return true;

        for (int val = 1; val <= N; ++val)
        {
            int assignedCount = 0;
            vector<Variable*> candidates;
            for (Variable* var : constraint.vars)
            {
                if (var->isAssigned())
                {
                    if (var->getAssignment() == val)
                        assignedCount++;
                    continue;
                }
                if (var->getDomain().contains(val))
                    candidates.push_back(var);
            }

            if (assignedCount > 1)
                return false;
            if (assignedCount == 1 || candidates.size() < 2)
                continue;

            bool sameRow = true;
            bool sameCol = true;
            bool sameBlock = true;

            int sharedRow = candidates[0]->row();
            int sharedCol = candidates[0]->col();
            int sharedBlock = candidates[0]->block();

            for (Variable* candidate : candidates)
            {
                sameRow = sameRow && (candidate->row() == sharedRow);
                sameCol = sameCol && (candidate->col() == sharedCol);
                sameBlock = sameBlock && (candidate->block() == sharedBlock);
            }

            if (kind == ConstraintKind::Block)
            {
                if (sameRow)
                {
                    Constraint* rowConstraint = findConstraintOfKind(network, candidates[0], ConstraintKind::Row);
                    if (rowConstraint == nullptr)
                        return false;

                    for (Variable* rowVar : rowConstraint->vars)
                    {
                        if (rowVar->block() == sharedBlock)
                            continue;
                        if (!eliminateValueFromVariable(network, trail, rowVar, val, assignedQueue, queuedAssigned, constraintQueue, queuedConstraints, assignedMap, pushed))
                            return false;
                    }
                }

                if (sameCol)
                {
                    Constraint* colConstraint = findConstraintOfKind(network, candidates[0], ConstraintKind::Col);
                    if (colConstraint == nullptr)
                        return false;

                    for (Variable* colVar : colConstraint->vars)
                    {
                        if (colVar->block() == sharedBlock)
                            continue;
                        if (!eliminateValueFromVariable(network, trail, colVar, val, assignedQueue, queuedAssigned, constraintQueue, queuedConstraints, assignedMap, pushed))
                            return false;
                    }
                }
            }
            else if ((kind == ConstraintKind::Row || kind == ConstraintKind::Col) && sameBlock)
            {
                Constraint* blockConstraint = findConstraintOfKind(network, candidates[0], ConstraintKind::Block);
                if (blockConstraint == nullptr)
                    return false;

                for (Variable* blockVar : blockConstraint->vars)
                {
                    if (kind == ConstraintKind::Row && blockVar->row() == sharedRow)
                        continue;
                    if (kind == ConstraintKind::Col && blockVar->col() == sharedCol)
                        continue;
                    if (!eliminateValueFromVariable(network, trail, blockVar, val, assignedQueue, queuedAssigned, constraintQueue, queuedConstraints, assignedMap, pushed))
                        return false;
                }
            }
        }

        return true;
    }

    bool applyNakedPairs(ConstraintNetwork& network, Constraint& constraint, Trail* trail, int N, queue<Variable*>& assignedQueue, unordered_set<Variable*>& queuedAssigned, queue<Constraint*>& constraintQueue, unordered_set<Constraint*>& queuedConstraints, unordered_map<Variable*, int>* assignedMap, unordered_set<Variable*>& pushed)
    {
        int base = N + 1;
        unordered_map<long long, vector<Variable*>> pairToVars;
        for (Variable* var : constraint.vars)
        {
            if (var->isAssigned())
                continue;
            Domain d = var->getDomain();
            if (d.size() != 2)
                continue;

            vector<int> values = d.getValues();
            sort(values.begin(), values.end());
            long long key = static_cast<long long>(values[0]) * base + values[1];
            pairToVars[key].push_back(var);
        }

        for (auto& pairEntry : pairToVars)
        {
            if (pairEntry.second.size() != 2)
                continue;

            int valueA = static_cast<int>(pairEntry.first / base);
            int valueB = static_cast<int>(pairEntry.first % base);
            Variable* pairVar1 = pairEntry.second[0];
            Variable* pairVar2 = pairEntry.second[1];

            for (Variable* var : constraint.vars)
            {
                if (var == pairVar1 || var == pairVar2 || var->isAssigned())
                    continue;

                if (!eliminateValueFromVariable(network, trail, var, valueA, assignedQueue, queuedAssigned, constraintQueue, queuedConstraints, assignedMap, pushed))
                    return false;
                if (!eliminateValueFromVariable(network, trail, var, valueB, assignedQueue, queuedAssigned, constraintQueue, queuedConstraints, assignedMap, pushed))
                    return false;
            }
        }

        return true;
    }

    void seedPropagationFromModifiedState(ConstraintNetwork& network, queue<Variable*>& assignedQueue, unordered_set<Variable*>& queuedAssigned, queue<Constraint*>& constraintQueue, unordered_set<Constraint*>& queuedConstraints)
    {
        ConstraintNetwork::ConstraintRefSet modifiedConstraints = network.getModifiedConstraints();
        for (Constraint* constraint : modifiedConstraints)
        {
            enqueueConstraint(constraint, constraintQueue, queuedConstraints);
            for (Variable* var : constraint->vars)
            {
                if (var->isAssigned())
                    enqueueAssignedVariable(var, assignedQueue, queuedAssigned);
            }
        }
    }

    bool runPropagation(ConstraintNetwork& network, Trail* trail, unordered_map<Variable*, int>* assignedMap, bool enableAdvancedPropagation)
    {
        int N = getBoardDimension(network);

        queue<Variable*> assignedQueue;
        unordered_set<Variable*> queuedAssigned;
        queue<Constraint*> constraintQueue;
        unordered_set<Constraint*> queuedConstraints;
        unordered_set<Variable*> pushed;

        seedPropagationFromModifiedState(network, assignedQueue, queuedAssigned, constraintQueue, queuedConstraints);

        while (!assignedQueue.empty() || !constraintQueue.empty())
        {
            if (!propagateAssignedValues(network, trail, assignedQueue, queuedAssigned, constraintQueue, queuedConstraints, assignedMap, pushed))
            {
                network.getModifiedConstraints();
                return false;
            }

            while (!constraintQueue.empty())
            {
                Constraint* constraint = constraintQueue.front();
                constraintQueue.pop();
                queuedConstraints.erase(constraint);

                if (!applyHiddenSingles(network, *constraint, trail, N, assignedQueue, queuedAssigned, constraintQueue, queuedConstraints, assignedMap, pushed))
                {
                    network.getModifiedConstraints();
                    return false;
                }

                if (enableAdvancedPropagation)
                {
                    if (!applyPointingAndClaiming(network, *constraint, trail, N, assignedQueue, queuedAssigned, constraintQueue, queuedConstraints, assignedMap, pushed))
                    {
                        network.getModifiedConstraints();
                        return false;
                    }
                    if (!applyNakedPairs(network, *constraint, trail, N, assignedQueue, queuedAssigned, constraintQueue, queuedConstraints, assignedMap, pushed))
                    {
                        network.getModifiedConstraints();
                        return false;
                    }
                }

                if (!assignedQueue.empty())
                    break;
            }
        }

        bool consistent = network.isConsistent();
        network.getModifiedConstraints();
        return consistent;
    }
}

// =====================================================================
// Constructors
// =====================================================================

BTSolver::BTSolver ( SudokuBoard input, Trail* _trail,  string val_sh, string var_sh, string cc )
: sudokuGrid( input.get_p(), input.get_q(), input.get_board() ), network( input )
{
	valHeuristics = val_sh;
	varHeuristics = var_sh;
	cChecks =  cc;

	trail = _trail;
}

// =====================================================================
// Consistency Checks
// =====================================================================

// Basic consistency check, no propagation done
bool BTSolver::assignmentsCheck ( void )
{
	for ( Constraint c : network.getConstraints() )
		if ( ! c.isConsistent() )
			return false;

	return true;
}

// =================================================================
// Arc Consistency
// =================================================================
bool BTSolver::arcConsistency ( void )
{
    vector<Variable*> toAssign;
    vector<Constraint*> RMC = network.getModifiedConstraints();
    for (int i = 0; i < RMC.size(); ++i)
    {
        vector<Variable*> LV = RMC[i]->vars;
        for (int j = 0; j < LV.size(); ++j)
        {
            if(LV[j]->isAssigned())
            {
                vector<Variable*> Neighbors = network.getNeighborsOfVariable(LV[j]);
                int assignedValue = LV[j]->getAssignment();
                for (int k = 0; k < Neighbors.size(); ++k)
                {
                    Domain D = Neighbors[k]->getDomain();
                    if(D.contains(assignedValue))
                    {
                        if (D.size() == 1)
                            return false;
                        if (D.size() == 2)
                            toAssign.push_back(Neighbors[k]);
                        trail->push(Neighbors[k]);
                        Neighbors[k]->removeValueFromDomain(assignedValue);
                    }
                }
            }
        }
    }
    if (!toAssign.empty())
    {
        for (int i = 0; i < toAssign.size(); ++i)
        {
            Domain D = toAssign[i]->getDomain();
            vector<int> assign = D.getValues();
            trail->push(toAssign[i]);
            toAssign[i]->assignValue(assign[0]);
        }
        return arcConsistency();
    }
    return network.isConsistent();
}

/**
 * Part 1 TODO: Implement the Forward Checking Heuristic
 *
 * This function will do both Constraint Propagation and check
 * the consistency of the network
 *
 * (1) If a variable is assigned then eliminate that value from
 *     the square's neighbors.
 *
 * Note: remember to trail.push variables before you change their domain
 * Return: a pair of a map and a bool. The map contains the pointers to all MODIFIED variables, mapped to their MODIFIED domain.
 * 		   The bool is true if assignment is consistent, false otherwise.
 */
pair<unordered_map<Variable*,Domain>,bool> BTSolver::forwardChecking ( void )
{
	unordered_map<Variable*, Domain> modifiedMap;
	unordered_set<Variable*> recentAssigned;
	unordered_set<Variable*> pushed;
	ConstraintNetwork::ConstraintRefSet modifiedConstraints = network.getModifiedConstraints();

	for ( Constraint* constraint : modifiedConstraints )
	{
		for ( Variable* var : constraint->vars )
		{
			if ( var->isAssigned() )
				recentAssigned.insert( var );
		}
	}

	for ( Variable* v : recentAssigned )
	{
		int assignedVal = v->getAssignment();
		ConstraintNetwork::VariableSet neighbors = network.getNeighborsOfVariable( v );

		for ( Variable* neighbor : neighbors )
		{
			if ( neighbor->isAssigned() )
			{
				if ( neighbor->getAssignment() == assignedVal )
				{
					network.getModifiedConstraints();
					return make_pair( modifiedMap, false );
				}
				continue;
			}
			if ( ! neighbor->isChangeable() )
				continue;
			if ( ! neighbor->getDomain().contains( assignedVal ) )
				continue;

			if (pushed.insert(neighbor).second)
				trail->push( neighbor );
			neighbor->removeValueFromDomain( assignedVal );

			if ( neighbor->getDomain().isEmpty() )
			{
				network.getModifiedConstraints();
				return make_pair( modifiedMap, false );
			}

			modifiedMap[neighbor] = neighbor->getDomain();
		}
	}

	bool consistent = network.isConsistent();
	network.getModifiedConstraints();
	return make_pair( modifiedMap, consistent );
}

/**
 * Part 2 TODO: Implement both of Norvig's Heuristics
 *
 * This function will do both Constraint Propagation and check
 * the consistency of the network
 *
 * (1) If a variable is assigned then eliminate that value from
 *     the square's neighbors.
 *
 * (2) If a constraint has only one possible place for a value
 *     then put the value there.
 *
 * Note: remember to trail.push variables before you change their domain
 * Return: a pair of a map and a bool. The map contains the pointers to all variables that were assigned during
 *         the whole NorvigCheck propagation, and mapped to the values that they were assigned.
 *         The bool is true if assignment is consistent, false otherwise.
 */
pair<unordered_map<Variable*,int>,bool> BTSolver::norvigCheck ( void )
{
    unordered_map<Variable*, int> assignedMap;
    bool consistent = runPropagation(network, trail, &assignedMap, false);
    return make_pair(assignedMap, consistent);
}

/**
 * Optional TODO: Implement your own advanced Constraint Propagation
 *
 * Completing the three tourn heuristic will automatically enter
 * your program into a tournament.
 */
bool BTSolver::getTournCC ( void )
{
    return runPropagation(network, trail, nullptr, true);
}

// =====================================================================
// Variable Selectors
// =====================================================================

// Basic variable selector, returns first unassigned variable
Variable* BTSolver::getfirstUnassignedVariable ( void )
{
	for ( Variable* v : network.getVariables() )
		if ( !(v->isAssigned()) )
			return v;

	// Everything is assigned
	return nullptr;
}

/**
 * Part 1 TODO: Implement the Minimum Remaining Value Heuristic
 *
 * Return: The unassigned variable with the smallest domain
 */
Variable* BTSolver::getMRV ( void )
{
    Variable* mrv = nullptr;
    int minDomainSize = -1;

    for ( Variable* v : network.getVariables() )
    {
        if ( v->isAssigned() )
            continue;

        int domainSize = v->getDomain().size();
        if ( mrv == nullptr || domainSize < minDomainSize )
        {
            minDomainSize = domainSize;
            mrv = v;
        }
    }

    return mrv;
}

/**
 * Part 2 TODO: Implement the Minimum Remaining Value Heuristic
 *                with Degree Heuristic as a Tie Breaker
 *
 * Return: The unassigned variable with the smallest domain and affecting the most unassigned neighbors.
 * 		   If there are multiple variables that have the same smallest domain with the same number
 * 		   of unassigned neighbors, add them to the vector of Variables.
 *         If there is only one variable, return the vector of size 1 containing that variable.
 */
vector<Variable*> BTSolver::MRVwithTieBreaker ( void )
{
    // Pass 1: Find minimum domain size and collect MRV candidates with degrees
    int minDomainSize = INT_MAX;
    vector<pair<Variable*, int>> candidates; // (variable, degree)

    for ( Variable* v : network.getVariables() )
    {
        if ( v->isAssigned() )
            continue;

        int domSize = v->getDomain().size();

        if ( domSize < minDomainSize )
        {
            minDomainSize = domSize;
            candidates.clear();
        }

        if ( domSize == minDomainSize )
        {
            int degree = 0;
            ConstraintNetwork::VariableSet neighbors = network.getNeighborsOfVariable( v );
            for ( Variable* neighbor : neighbors )
            {
                if ( !neighbor->isAssigned() )
                    degree++;
            }
            candidates.push_back( make_pair( v, degree ) );
        }
    }

    if ( candidates.empty() )
        return { nullptr };

    if ( candidates.size() == 1 )
        return { candidates[0].first };

    // Pass 2: Find max degree and collect result
    int maxDegree = -1;
    for ( auto& p : candidates )
        if ( p.second > maxDegree )
            maxDegree = p.second;

    vector<Variable*> result;
    for ( auto& p : candidates )
        if ( p.second == maxDegree )
            result.push_back( p.first );

    return result;
}

/**
 * Optional TODO: Implement your own advanced Variable Heuristic
 *
 * Completing the three tourn heuristic will automatically enter
 * your program into a tournament.
 */
Variable* BTSolver::getTournVar ( void )
{
    Variable* best = nullptr;
    int bestDomainSize = INT_MAX;
    int bestWeightedDegree = -1;
    int bestDegree = -1;

    for (Variable* v : network.getVariables())
    {
        if (v->isAssigned())
            continue;

        int domainSize = v->getDomain().size();
        ConstraintNetwork::VariableSet neighbors = network.getNeighborsOfVariable(v);

        int degree = 0;
        int weightedDegree = 0;
        for (Variable* neighbor : neighbors)
        {
            if (neighbor->isAssigned())
                continue;

            degree++;
            int nSize = neighbor->getDomain().size();
            if (nSize <= 1)
                weightedDegree += 1000;
            else
                weightedDegree += (1000 / nSize);
        }

        bool isBetter = false;
        if (best == nullptr)
            isBetter = true;
        else if (domainSize < bestDomainSize)
            isBetter = true;
        else if (domainSize == bestDomainSize && weightedDegree > bestWeightedDegree)
            isBetter = true;
        else if (domainSize == bestDomainSize && weightedDegree == bestWeightedDegree && degree > bestDegree)
            isBetter = true;
        else if (domainSize == bestDomainSize && weightedDegree == bestWeightedDegree && degree == bestDegree)
        {
            if (v->row() < best->row() || (v->row() == best->row() && v->col() < best->col()))
                isBetter = true;
        }

        if (isBetter)
        {
            best = v;
            bestDomainSize = domainSize;
            bestWeightedDegree = weightedDegree;
            bestDegree = degree;
        }
    }

    return best;
}

// =====================================================================
// Value Selectors
// =====================================================================

// Default Value Ordering
vector<int> BTSolver::getValuesInOrder ( Variable* v )
{
	vector<int> values = v->getDomain().getValues();
	sort( values.begin(), values.end() );
	return values;
}

/**
 * Part 1 TODO: Implement the Least Constraining Value Heuristic
 *
 * The Least constraining value is the one that will knock the least
 * values out of it's neighbors domain.
 *
 * Return: A list of v's domain sorted by the LCV heuristic
 *         The LCV is first and the MCV is last
 */
vector<int> BTSolver::getValuesLCVOrder ( Variable* v )
{
    vector<int> values = v->getDomain().getValues();
    ConstraintNetwork::VariableSet neighbors = network.getNeighborsOfVariable( v );

    // For each value, count how many neighbor domain values it would eliminate
    vector<pair<int,int>> valueConstraintCount; // (count, value)

    for ( int val : values )
    {
        int count = 0;
        for ( Variable* neighbor : neighbors )
        {
            if ( neighbor->isAssigned() )
                continue;
            if ( neighbor->getDomain().contains( val ) )
                count++;
        }
        valueConstraintCount.push_back( make_pair( count, val ) );
    }

    // Sort ascending by count (least constraining first)
    sort( valueConstraintCount.begin(), valueConstraintCount.end() );

    vector<int> sortedValues;
    for ( auto& p : valueConstraintCount )
        sortedValues.push_back( p.second );

    return sortedValues;
}

/**
 * Optional TODO: Implement your own advanced Value Heuristic
 *
 * Completing the three tourn heuristic will automatically enter
 * your program into a tournament.
 */
vector<int> BTSolver::getTournVal ( Variable* v )
{
    if (v == nullptr)
        return vector<int>();

    vector<int> values = v->getDomain().getValues();
    if (values.size() <= 1)
        return values;

    ConstraintNetwork::VariableSet neighbors = network.getNeighborsOfVariable(v);
    ConstraintNetwork::ConstraintRefSet relatedConstraints = network.getConstraintsContainingVariable(v);

    struct ValueScore
    {
        int value;
        int pruneCount;
        int rarityScore;
        int forcedNeighborScore;
    };

    vector<ValueScore> scores;
    scores.reserve(values.size());

    for (int val : values)
    {
        int pruneCount = 0;
        int forcedNeighborScore = 0;
        for (Variable* neighbor : neighbors)
        {
            if (neighbor->isAssigned())
            {
                if (neighbor->getAssignment() == val)
                    pruneCount += 1000000;
                continue;
            }
            if (!neighbor->getDomain().contains(val))
                continue;

            pruneCount++;
            if (neighbor->getDomain().size() == 2)
                forcedNeighborScore++;
        }

        int rarityScore = 0;
        for (Constraint* c : relatedConstraints)
        {
            int occurrences = 0;
            bool alreadyAssignedInConstraint = false;
            for (Variable* cv : c->vars)
            {
                if (cv->isAssigned())
                {
                    if (cv->getAssignment() == val)
                    {
                        alreadyAssignedInConstraint = true;
                        break;
                    }
                    continue;
                }

                if (cv->getDomain().contains(val))
                    occurrences++;
            }

            if (!alreadyAssignedInConstraint)
                rarityScore += occurrences;
        }

        scores.push_back({val, pruneCount, rarityScore, forcedNeighborScore});
    }

    sort(scores.begin(), scores.end(), [](const ValueScore& a, const ValueScore& b)
    {
        if (a.pruneCount != b.pruneCount)
            return a.pruneCount < b.pruneCount;
        // Lower occurrence count means the value is rarer in related constraints.
        if (a.rarityScore != b.rarityScore)
            return a.rarityScore < b.rarityScore;
        if (a.forcedNeighborScore != b.forcedNeighborScore)
            return a.forcedNeighborScore > b.forcedNeighborScore;
        return a.value < b.value;
    });

    vector<int> ordered;
    ordered.reserve(scores.size());
    for (const ValueScore& score : scores)
        ordered.push_back(score.value);

    return ordered;
}

// =====================================================================
// Engine Functions
// =====================================================================

int BTSolver::solve ( float time_left)
{
	if (time_left <= 0.0)
		return -1;
	double elapsed_time = 0.0;
    clock_t begin_clock = clock();

	if ( hasSolution )
		return 0;

	// Variable Selection
	Variable* v = selectNextVariable();

	if ( v == nullptr )
	{
		for ( Variable* var : network.getVariables() )
		{
			// If all variables haven't been assigned
			if ( ! ( var->isAssigned() ) )
			{
				return 0;
			}
		}

		// Success
		hasSolution = true;
		return 0;
	}

	// Attempt to assign a value
	for ( int i : getNextValues( v ) )
	{
		// Store place in trail and push variable's state on trail
		trail->placeTrailMarker();
		trail->push( v );

		// Assign the value
		v->assignValue( i );

		// Propagate constraints, check consistency, recurse
		if ( checkConsistency() ) {
			clock_t end_clock = clock();
			elapsed_time += (float)(end_clock - begin_clock)/ CLOCKS_PER_SEC;
			double new_start_time = time_left - elapsed_time;
			int check_status = solve(new_start_time);
			if(check_status == -1) {
			    return -1;
			}

		}

		// If this assignment succeeded, return
		if ( hasSolution )
			return 0;

		// Otherwise backtrack
		trail->undo();
	}
	return 0;
}

bool BTSolver::checkConsistency ( void )
{
	if ( cChecks == "forwardChecking" )
		return forwardChecking().second;

	if ( cChecks == "norvigCheck" )
		return norvigCheck().second;

	if ( cChecks == "tournCC" )
		return getTournCC();

	return assignmentsCheck();
}

Variable* BTSolver::selectNextVariable ( void )
{
	if ( varHeuristics == "MinimumRemainingValue" )
		return getMRV();

	if ( varHeuristics == "MRVwithTieBreaker" )
		return MRVwithTieBreaker()[0];

	if ( varHeuristics == "tournVar" )
		return getTournVar();

	return getfirstUnassignedVariable();
}

vector<int> BTSolver::getNextValues ( Variable* v )
{
	if ( valHeuristics == "LeastConstrainingValue" )
		return getValuesLCVOrder( v );

	if ( valHeuristics == "tournVal" )
		return getTournVal( v );

	return getValuesInOrder( v );
}

bool BTSolver::haveSolution ( void )
{
	return hasSolution;
}

SudokuBoard BTSolver::getSolution ( void )
{
	return network.toSudokuBoard ( sudokuGrid.get_p(), sudokuGrid.get_q() );
}

ConstraintNetwork BTSolver::getNetwork ( void )
{
	return network;
}
