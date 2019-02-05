import read, copy
from util import *
from logical_classes import *
import pdb

verbose = 0

class KnowledgeBase(object):
    def __init__(self, facts=[], rules=[]):
        self.facts = facts
        self.rules = rules
        self.ie = InferenceEngine()

    def __repr__(self):
        return 'KnowledgeBase({!r}, {!r})'.format(self.facts, self.rules)

    def __str__(self):
        string = "Knowledge Base: \n"
        string += "\n".join((str(fact) for fact in self.facts)) + "\n"
        string += "\n".join((str(rule) for rule in self.rules))
        return string

    def _get_fact(self, fact):
        """INTERNAL USE ONLY
        Get the fact in the KB that is the same as the fact argument

        Args:
            fact (Fact): Fact we're searching for

        Returns:
            Fact: matching fact
        """
        for kbfact in self.facts:
            if fact == kbfact:
                return kbfact

    def _get_rule(self, rule):
        """INTERNAL USE ONLY
        Get the rule in the KB that is the same as the rule argument

        Args:
            rule (Rule): Rule we're searching for

        Returns:
            Rule: matching rule
        """
        for kbrule in self.rules:
            if rule == kbrule:
                return kbrule

    def kb_add(self, fact_rule):
        """Add a fact or rule to the KB
        Args:
            fact_rule (Fact|Rule) - the fact or rule to be added
        Returns:
            None
        """
        printv("Adding {!r}", 1, verbose, [fact_rule])
        if isinstance(fact_rule, Fact):
            if fact_rule not in self.facts:
                self.facts.append(fact_rule)
                for rule in self.rules:
                    self.ie.fc_infer(fact_rule, rule, self)
            else:
                if fact_rule.supported_by:
                    ind = self.facts.index(fact_rule)
                    for f in fact_rule.supported_by:
                        self.facts[ind].supported_by.append(f)
                else:
                    ind = self.facts.index(fact_rule)
                    self.facts[ind].asserted = True
        elif isinstance(fact_rule, Rule):
            if fact_rule not in self.rules:
                self.rules.append(fact_rule)
                for fact in self.facts:
                    self.ie.fc_infer(fact, fact_rule, self)
            else:
                if fact_rule.supported_by:
                    ind = self.rules.index(fact_rule)
                    for f in fact_rule.supported_by:
                        self.rules[ind].supported_by.append(f)
                else:
                    ind = self.rules.index(fact_rule)
                    self.rules[ind].asserted = True

    def kb_assert(self, fact_rule):
        """Assert a fact or rule into the KB

        Args:
            fact_rule (Fact or Rule): Fact or Rule we're asserting
        """
        printv("Asserting {!r}", 0, verbose, [fact_rule])
        self.kb_add(fact_rule)

    def kb_ask(self, fact):
        """Ask if a fact is in the KB

        Args:
            fact (Fact) - Statement to be asked (will be converted into a Fact)

        Returns:
            listof Bindings|False - list of Bindings if result found, False otherwise
        """
        print("Asking {!r}".format(fact))
        if factq(fact):
            f = Fact(fact.statement)
            bindings_lst = ListOfBindings()
            # ask matched facts
            for fact in self.facts:
                binding = match(f.statement, fact.statement)
                if binding:
                    bindings_lst.add_bindings(binding, [fact])

            return bindings_lst if bindings_lst.list_of_bindings else []

        else:
            print("Invalid ask:", fact.statement)
            return []

    def kb_remove(self, fact_or_rule):
        #if fact is not supported but is asserted --> remove
        #if rule is not supported AND not asserted --> remove
        if len(fact_or_rule.supported_by) == 0: # if not supported by anything--> check for fact or rule
            if (factq(fact_or_rule)) or ((not factq(fact_or_rule)) and not fact_or_rule.asserted):
                if factq(fact_or_rule): #if it is a fact --> remove it from facts list
                    self.facts.remove(fact_or_rule)  # removed the fact from list of facts
                else: #if it is a rule --> remove it from rule list
                    self.rules.remove(fact_or_rule)

                for f in fact_or_rule.supports_facts:  # run through all the facts that removed fact supports
                    for support in f.supported_by: #supported_by is list of list, must search through all of the list in supported_by
                        if fact_or_rule in support:   #if fact_or_rule is in the supports list
                            f.supported_by.remove(support)  # update supported by
                    self.kb_remove(f) # recursively call remove
                for r in fact_or_rule.supports_rules:  # run through all the rules that retracted fact supports
                    for support in r.supported_by:
                        if fact_or_rule in support:
                            r.supported_by.remove(support)  # update supported by
                    self.kb_remove(r)  # recursively call remove on this rule

    def kb_retract(self, fact_or_rule):
        """Retract a fact from the KB

        Args:
            fact (Fact) - Fact to be retracted

        Returns:
            None
        """
        printv("Retracting {!r}", 0, verbose, [fact_or_rule])
        ####################################################
        # Student code goes here
        #always being retracted --> set asserted flag to false, check if still supported
        #if still supported --> do nothing
        #if no longer supported then remove
        #if a rule don't do anything
        if factq(fact_or_rule): #if it is a fact
            fact = self._get_fact(fact_or_rule)
            fact.asserted=False; #change the asserted flag to False
            self.kb_remove(fact)


class InferenceEngine(object):
    def fc_infer(self, fact, rule, kb):
        """Forward-chaining to infer new facts and rules

        Args:
            fact (Fact) - A fact from the KnowledgeBase
            rule (Rule) - A rule from the KnowledgeBase
            kb (KnowledgeBase) - A KnowledgeBase

        Returns:
            Nothing            
        """
        printv('Attempting to infer from {!r} and {!r} => {!r}', 1, verbose,
            [fact.statement, rule.lhs, rule.rhs])
        ####################################################
        # have to check if the left hand side of the rule only has one statement -> infer a fact directly
        # if LHS has more than 1 statement -> only compare first statement --> infer new rule
        # Student code goes here
        matches=match(rule.lhs[0], fact.statement) #returns list of bindings or false
        if matches: #if there IS a match between the first element of the lhs and the fact
            if len(rule.lhs)==1:  #check if there is only one statement on the LHS --> instantiate a fact
                new_fact_statement=instantiate(rule.rhs, matches) #returns a statement
                new_fact=Fact(new_fact_statement, [[fact, rule]]) #returns a new fact
                kb.kb_add(new_fact)
                #add to supports facts
                fact.supports_facts.append(kb._get_fact(new_fact))
                rule.supports_facts.append(kb._get_fact(new_fact))
            else: #if the LHS has more than one statement --> instantiate a new rule
                new_lhs=[]
                for left in rule.lhs[1:]: #run through all of the other statements in the LHS
                    new_lhs.append(instantiate(left, matches))
                new_rhs_statement=instantiate(rule.rhs, matches)
                new_rule=Rule([new_lhs, new_rhs_statement], [[fact, rule]]) #returns new rule
                kb.kb_add(new_rule)
                fact.supports_rules.append(kb._get_rule(new_rule))
                rule.supports_rules.append(kb._get_rule(new_rule))
                #instantiate with the bindings found --> return new statement, store in list that is the new LHS, repeat over all of the LHS other than the first one

