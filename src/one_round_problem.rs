pub mod one_round {
    use core::fmt::Debug;
    use core::hash::Hash;
    use core::ops::Add;
    use itertools::Itertools;
    use std::collections::HashMap;
    use std::collections::HashSet;
    use std::str::FromStr;
    use std::string::ParseError;
    use std::vec;

    /// The vals vector has digits and we wish to increase the number that vals represents by 1. Every digit can be at most modulo-1
    /// The return value is true if the resulting number is 0 or in other words every element in vals have value 0
    pub fn number_system_increase<T>(vals: &mut [T], modulo: T) -> bool
    where
        T: Add<usize, Output = T>,
        T: PartialEq<T>,
        T: Default + Copy + std::cmp::PartialOrd,
    {
        let mut remainder: usize = 1;

        for v in vals.as_mut() {
            if remainder == 0 {
                break;
            }
            *v = *v + remainder;
            remainder = 0;

            if *v >= modulo {
                remainder = 1;
                *v = Default::default();
            }
        }

        for v in vals.as_mut() {
            if *v != T::default() {
                return false;
            }
        }

        return true;
    }

    /// An LCL problem given with node states and edge states with non compact form on the labels.
    #[derive(Debug, PartialEq, Clone)]
    pub struct UnshortenedProblem<
        T: FromStr + Hash + Copy + std::cmp::Eq + Debug + Default + std::cmp::Ord,
    > {
        delta_deg_size: usize, //The size of node states or in other words degree of nodes.
        delta_edge_size: usize, //The size of edge states or in other words size of edges.
        node_states: Vec<Vec<T>>,
        edge_states: Vec<Vec<T>>,
    }

    impl<T: FromStr + Hash + Copy + std::cmp::Eq + Debug + Default + std::cmp::Ord>
        UnshortenedProblem<T>
    {
        pub fn new(
            delta_deg_size: usize,
            delta_edge_size: usize,
            node_states: Vec<Vec<T>>,
            mut edge_states: Vec<Vec<T>>,
        ) -> UnshortenedProblem<T> {
            for edge in edge_states.iter_mut() {
                edge.sort();
            }
            UnshortenedProblem {
                delta_deg_size,
                delta_edge_size,
                node_states,
                edge_states,
            }
        }

        pub fn from_string(
            delta_deg: usize,
            delta_edge: usize,
            node_states_str: &str,
            edge_states_str: &str,
        ) -> Result<UnshortenedProblem<T>, <T as FromStr>::Err> {
            //Every line in the node_states need to have delta_deg number of characters

            let mut node_states: Vec<Vec<T>> = vec![];
            for line in node_states_str.lines() {
                let mut node_state: Vec<T> = vec![];
                for label_character in line.split_whitespace() {
                    let label = label_character.parse::<T>()?;
                    node_state.push(label);
                }
                node_states.push(node_state);
            }

            let mut edge_states: Vec<Vec<T>> = vec![];
            for line in edge_states_str.lines() {
                let mut edge_state: Vec<T> = vec![];
                for label_character in line.split_whitespace() {
                    let label = label_character.parse::<T>()?;
                    edge_state.push(label);
                }
                edge_states.push(edge_state);
            }

            Ok(UnshortenedProblem::new(
                delta_deg,
                delta_edge,
                node_states,
                edge_states,
            ))
        }

        pub fn edge_exist(&self, edge_to_check: &mut Vec<T>) -> bool {
            edge_to_check.sort();
            for edge in self.edge_states.iter() {
                if edge == edge_to_check {
                    return true;
                }
            }

            return false;
        }

        pub fn node_states_ref(&self) -> &Vec<Vec<T>> {
            return &self.node_states;
        }

        pub fn edge_states_ref(&self) -> &Vec<Vec<T>> {
            return &self.edge_states;
        }
    }

    /// The struct that stores the mapping between two UnshortenedProblem.
    #[derive(Debug, PartialEq, Clone)]
    pub struct LabelMapping {
        input_number_node_states: usize,
        output_number_node_states: usize,
        node_states_mapping: Vec<usize>, //The mapping of input nodes states to the output states.
        node_states_detailed_mapping: Vec<Vec<usize>>, //Using the node_states_mapping we need to map a given node_state 'v' to node_states_mapping[v] in all possible ways. This is always a permutation of the numbers 0..delta_deg
    }

    impl LabelMapping {
        pub fn new(
            delta_deg: usize,
            input_node_states_number: usize,
            output_node_states_number: usize,
        ) -> LabelMapping {
            LabelMapping {
                input_number_node_states: input_node_states_number,
                output_number_node_states: output_node_states_number,
                node_states_mapping: vec![0; input_node_states_number],
                node_states_detailed_mapping: vec![
                    (0..delta_deg).collect();
                    input_node_states_number
                ],
            }
        }

        pub fn new_from_given(
            input_node_states_number: usize,
            output_node_states_number: usize,
            node_states_mapping: Vec<usize>,
            node_states_detailed_mapping: Vec<Vec<usize>>,
        ) -> LabelMapping {
            LabelMapping {
                input_number_node_states: input_node_states_number,
                output_number_node_states: output_node_states_number,
                node_states_mapping: node_states_mapping,
                node_states_detailed_mapping: node_states_detailed_mapping,
            }
        }

        pub fn summarized_labeling_mapping<
            T: FromStr + Hash + Copy + std::cmp::Eq + Debug + Default + std::cmp::Ord,
        >(
            &self,
            solvability_problem: &SolvabilityProblem<T>,
        ) -> HashMap<T, HashSet<T>> {
            let mut summarized_labels = HashMap::new();

            for (ind_state, state_map) in self.node_states_mapping.iter().enumerate() {
                for (ind_label, label_map) in self.node_states_detailed_mapping[ind_state]
                    .iter()
                    .enumerate()
                {
                    let input_label =
                        solvability_problem.input_problem.node_states[ind_state][ind_label];
                    let output_label =
                        solvability_problem.output_problem.node_states[*state_map][*label_map];

                    summarized_labels
                        .entry(input_label)
                        .or_insert(HashSet::new())
                        .insert(output_label);
                }
            }

            summarized_labels
        }
    }

    #[derive(Debug, PartialEq, Clone)]
    pub struct SolvabilityProblem<
        T: FromStr + Hash + Copy + std::cmp::Eq + Debug + Default + std::cmp::Ord,
    > {
        pub input_problem: UnshortenedProblem<T>,
        pub output_problem: UnshortenedProblem<T>,
        pub label_map: LabelMapping,
        pub labels_summarized_mapping: HashMap<T, HashSet<T>>, // For every input label character we collect all of the possible type of labels if can take given the current mapping
    }

    impl<T: FromStr + Hash + Copy + std::cmp::Eq + Debug + Default + std::cmp::Ord>
        SolvabilityProblem<T>
    {
        pub fn new(
            input_problem: &UnshortenedProblem<T>,
            output_problem: &UnshortenedProblem<T>,
        ) -> SolvabilityProblem<T> {
            SolvabilityProblem {
                input_problem: input_problem.clone(),
                output_problem: output_problem.clone(),
                label_map: LabelMapping::new(
                    input_problem.delta_deg_size,
                    input_problem.node_states.len(),
                    output_problem.node_states.len(),
                ),
                labels_summarized_mapping: HashMap::new(),
            }
        }

        pub fn new_from_given(
            input_problem: &UnshortenedProblem<T>,
            output_problem: &UnshortenedProblem<T>,
            label_map: LabelMapping,
        ) -> SolvabilityProblem<T> {
            SolvabilityProblem {
                input_problem: input_problem.clone(),
                output_problem: output_problem.clone(),
                label_map: label_map,
                labels_summarized_mapping: HashMap::new(),
            }
        }

        pub fn print_out_labelling(&self) {
            println!("Input problem: {:?}", self.input_problem);
            println!("Output problem: {:?}", self.output_problem);
            println!("Label mapping: {:?}", self.label_map);

            for (ind_state, state_map) in self.label_map.node_states_mapping.iter().enumerate() {
                println!(
                    "Input node state: {:?}",
                    self.input_problem.node_states[ind_state]
                );
                let output_labels: Vec<T> = self.label_map.node_states_detailed_mapping[ind_state]
                    .iter()
                    .map(|x| self.output_problem.node_states[*state_map][*x])
                    .collect();
                println!("Output node state in order: {:?}", output_labels);
            }
            println!(
                "The summarized label mapping: {:?}",
                self.label_map.summarized_labeling_mapping(self)
            );
        }

        /// Given the label_mapping and an edge we wish to check the function checks if all possible mappings of the edge is still possible
        fn check_satisfiability_edges(
            &self,
            label_ind: usize,
            edge: &Vec<T>,
            labels_summarized: &HashMap<T, HashSet<T>>,
            choice_of_map: &mut Vec<T>, //The possible labels the input labels choose.
        ) -> bool {
            if label_ind == edge.len() {
                let mut created_edge: Vec<T> = choice_of_map.clone();

                //println!("Testing the following edge: {:?}, with mapped labelling of {:?}", edge, created_edge);

                // If the created edge does not exist in the output problem's edges then this is an incorrect labelling
                if !self.output_problem.edge_exist(&mut created_edge) {
                    return false;
                }
                return true;
            }

            for label in labels_summarized.get(&edge[label_ind]).unwrap().iter() {
                choice_of_map[label_ind] = *label;

                if self.check_satisfiability_edges(
                    label_ind + 1,
                    edge,
                    labels_summarized,
                    choice_of_map,
                ) == false
                {
                    return false;
                }
            }

            return true;
        }

        /// Checks if the current label_mapping is a correct labelling
        pub fn check_satisfiability(&self) -> bool {
            let labels_summarized = self.label_map.summarized_labeling_mapping(self);

            for edge in self.input_problem.edge_states.iter() {
                let mut choice_of_map: Vec<T> =
                    vec![T::default(); self.input_problem.delta_edge_size];
                if self.check_satisfiability_edges(0, edge, &labels_summarized, &mut choice_of_map)
                    == false
                {
                    return false;
                }
            }

            true
        }

        /// Tries every permutation for node state to node state so basically (delta_deg!) * |node_state| number of tries in worst case.
        fn check_every_detailed_mapping(&mut self, node_state_index: usize) -> bool {
            if node_state_index == self.input_problem.node_states.len() {
                if self.check_satisfiability() {
                    return true;
                }
                return false;
            }

            let curr_permutation =
                self.label_map.node_states_detailed_mapping[node_state_index].clone();
            for permi in curr_permutation
                .iter()
                .permutations(self.input_problem.delta_deg_size)
            {
                self.label_map.node_states_detailed_mapping[node_state_index] =
                    permi.into_iter().cloned().collect();
                if self.check_every_detailed_mapping(node_state_index + 1) {
                    return true;
                }
            }

            return false;
        }

        /// The functions checks if there exists and algorithm that solves output problem from input_problem in zero rounds.
        pub fn search_for_solution(&mut self) -> bool {
            loop {
                if self.check_every_detailed_mapping(0) {
                    return true;
                }

                if number_system_increase(
                    &mut self.label_map.node_states_mapping,
                    self.output_problem.node_states.len(),
                ) {
                    break;
                }
            }

            return false;
        }
    }
}

#[cfg(test)]
mod tests {

    use std::collections::{HashMap, HashSet};

    use one_round::{number_system_increase, LabelMapping, SolvabilityProblem, UnshortenedProblem};

    use super::*;

    #[test]
    fn parsing() {
        let p_str: UnshortenedProblem<char> =
            UnshortenedProblem::from_string(3, 2, "M M M\nP O O", "M P\nO O\nO M").unwrap();
        let p_corr: UnshortenedProblem<char> = UnshortenedProblem::new(
            3,
            2,
            vec![vec!['M', 'M', 'M'], vec!['P', 'O', 'O']],
            vec![vec!['M', 'P'], vec!['O', 'O'], vec!['O', 'M']],
        );
        assert_eq!(p_str, p_corr);
    }

    #[test]
    fn problem_creation() {
        let problem_in: UnshortenedProblem<char> =
            UnshortenedProblem::from_string(3, 2, "M M M\nP O O", "M P\nO O\nO M").unwrap();
        let problem_out: UnshortenedProblem<char> = UnshortenedProblem::from_string(
            3,
            2,
            "A A X\nB B Y",
            "A B\nA A\nA Y\nB X\nB B\nX B\nY A\nX Y",
        )
        .unwrap();
        let prob = SolvabilityProblem::new(&problem_in, &problem_out);
        prob.print_out_labelling();

        let mut summarized_labelling: HashMap<char, HashSet<char>> = HashMap::new();
        summarized_labelling.insert('P', HashSet::from_iter(vec!['A']));
        summarized_labelling.insert('O', HashSet::from_iter(vec!['A', 'X']));
        summarized_labelling.insert('M', HashSet::from_iter(vec!['A', 'X']));

        assert_eq!(
            prob.label_map.summarized_labeling_mapping(&prob),
            summarized_labelling
        );
    }

    #[test]
    fn checking_if_edges_exist() {
        let problem1: UnshortenedProblem<char> =
            UnshortenedProblem::from_string(3, 2, "M M M\nP O O", "M P\nO O\nO M").unwrap();
        let problem2: UnshortenedProblem<char> = UnshortenedProblem::from_string(
            3,
            2,
            "A A X\nC C Y",
            "A B\nA A\nA Y\nB X\nB B\nX B\nY A\nX Y",
        )
        .unwrap();

        assert_eq!(problem1.edge_exist(&mut vec!['M', 'O']), true);
        assert_eq!(problem1.edge_exist(&mut vec!['O', 'M']), true);
        assert_eq!(problem1.edge_exist(&mut vec!['M', 'M']), false);

        assert_eq!(problem2.edge_exist(&mut vec!['X', 'B']), true);
        assert_eq!(problem2.edge_exist(&mut vec!['Y', 'X']), true);
        assert_eq!(problem2.edge_exist(&mut vec!['A', 'X']), false);
        assert_eq!(problem2.edge_exist(&mut vec!['M', 'M']), false);
    }

    #[test]
    fn correct_and_inc_labelling_checking() {
        let problem_in: UnshortenedProblem<char> =
            UnshortenedProblem::from_string(3, 2, "M M M\nP O O", "M P\nO O\nO M").unwrap();
        let problem_out: UnshortenedProblem<char> = UnshortenedProblem::from_string(
            3,
            2,
            "A A X\nB B Y",
            "A B\nA A\nA Y\nB X\nB B\nX B\nY A\nX Y",
        )
        .unwrap();
        let prob = SolvabilityProblem::new(&problem_in, &problem_out);
        prob.print_out_labelling();
        assert_eq!(prob.check_satisfiability(), false);

        let mut label_correct = LabelMapping::new_from_given(
            prob.input_problem.node_states_ref().len(),
            prob.output_problem.node_states_ref().len(),
            vec![0, 1],
            vec![vec![0, 1, 2], vec![2, 1, 0]],
        );

        let prob_new = SolvabilityProblem::new_from_given(&problem_in, &problem_out, label_correct);
        prob_new.print_out_labelling();
        assert_eq!(prob_new.check_satisfiability(), true);
    }

    #[test]
    fn find_correct_labelling() {
        let problem_in: UnshortenedProblem<char> =
            UnshortenedProblem::from_string(3, 2, "M M M\nP O O", "M P\nO O\nO M").unwrap();
        let problem_out: UnshortenedProblem<char> = UnshortenedProblem::from_string(
            3,
            2,
            "A A X\nB B Y",
            "A B\nA A\nA Y\nB X\nB B\nX B\nY A\nX Y",
        )
        .unwrap();
        let mut prob = SolvabilityProblem::new(&problem_in, &problem_out);
        prob.print_out_labelling();
        assert_eq!(prob.check_satisfiability(), false);

        assert_eq!(prob.search_for_solution(), true);
        println!("\n\n");
        prob.print_out_labelling();
    }

    #[test]
    fn no_correct_labelling() {
        let problem_in: UnshortenedProblem<char> =
            UnshortenedProblem::from_string(3, 2, "M M M\nP O O", "M P\nO O\nO M").unwrap();
        let problem_out: UnshortenedProblem<char> =
            UnshortenedProblem::from_string(3, 2, "T H H\nT H T\nT T H\nT T T", "H T").unwrap();
        let mut prob = SolvabilityProblem::new(&problem_in, &problem_out);
        prob.print_out_labelling();
        assert_eq!(prob.check_satisfiability(), false);

        assert_eq!(prob.search_for_solution(), false);
        println!("\n\n");
        prob.print_out_labelling();
    }

    #[test]
    fn one_way_possible_labelling() {
        let problem_in: UnshortenedProblem<char> = UnshortenedProblem::from_string(
            3,
            2,
            "A A A\nA A X\nB B B\nB B Y",
            "A B\nA Y\nX B\nX Y\nX X\nX Y\nY Y",
        )
        .unwrap();
        let problem_out: UnshortenedProblem<char> = UnshortenedProblem::from_string(
            3,
            2,
            "A A X\nB B Y",
            "A B\nA A\nA Y\nB X\nB B\nX B\nY A\nX Y",
        )
        .unwrap();
        let mut prob_forward = SolvabilityProblem::new(&problem_in, &problem_out);

        assert_eq!(prob_forward.search_for_solution(), true);
        println!("\n\n");
        prob_forward.print_out_labelling();

        let mut prob_backward = SolvabilityProblem::new(&problem_out, &problem_in);
        assert_eq!(prob_backward.search_for_solution(), false);
        println!("\n\n");
        prob_backward.print_out_labelling();
    }

    #[test]
    fn number_system() {
        let mut val1 = vec![0, 1, 2, 3];
        let mut val2 = vec![1, 1, 2, 3];
        let mut val3 = vec![3, 1, 2, 3];
        let mut val4 = vec![3, 3, 2, 3];
        let mut val5 = vec![3, 3, 3, 3];
        let modi = 4;

        number_system_increase(&mut val1, modi);
        assert_eq!(val1, vec![1, 1, 2, 3]);

        number_system_increase(&mut val2, modi);
        assert_eq!(val2, vec![2, 1, 2, 3]);

        number_system_increase(&mut val3, modi);
        assert_eq!(val3, vec![0, 2, 2, 3]);

        number_system_increase(&mut val4, modi);
        assert_eq!(val4, vec![0, 0, 3, 3]);

        number_system_increase(&mut val5, modi);
        assert_eq!(val5, vec![0, 0, 0, 0]);
    }
}
