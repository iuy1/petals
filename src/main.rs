use core::str;
use either::Either;
use std::collections::HashMap;
use std::ops::IndexMut;
use std::{env, fs};

extern crate strum;
#[macro_use]
extern crate strum_macros;

type VariableName = String;
type Command = String;
type Number = f64;

#[derive(Display, Debug, Clone)]
enum Variable {
  None,
  Number(Number),
  String(String),
  List(Vec<Variable>),
}

#[derive(Display, Debug, PartialEq, Clone)]
enum Operator {
  None,
  Add,
  Subtract,
  Multiply,
  Divide,
  FloorDivide,
  Lesser,
  Greater,
  LesserEqual,
  GreaterEqual,
  Equal,
  NotEqual,
  Assign,
  ParenthesisLeft,
  ParenthesisRight,
  Get,
  SquareBracketLeft,
  SquareBracketRight,
  CreateList,
  CurlyBraketLeft,
  // CurlyBraketRight,
  Semicolon,
}
#[derive(PartialEq)]
enum Associativity {
  Left,
  Right,
}

impl From<&str> for Operator {
  fn from(value: &str) -> Self {
    match value {
      "+" => Operator::Add,
      "-" => Operator::Subtract,
      "*" => Operator::Multiply,
      "/" => Operator::Divide,
      "//" => Operator::FloorDivide,
      "<" => Operator::Lesser,
      ">" => Operator::Greater,
      "<=" => Operator::LesserEqual,
      ">=" => Operator::GreaterEqual,
      "==" => Operator::Equal,
      "!=" => Operator::NotEqual,
      "=" => Operator::Assign,
      "(" => Operator::ParenthesisLeft,
      ")" => Operator::ParenthesisRight,
      "[" => Operator::SquareBracketLeft,
      "]" => Operator::SquareBracketRight,
      // "{" => Operator::CurlyBraketLeft,
      // "}" => Operator::CurlyBraketRight,
      ";" => Operator::Semicolon,
      _ => Operator::None,
    }
  }
}

impl Operator {
  fn associativity(&self) -> Associativity {
    match self {
      Operator::Assign => Associativity::Right,
      Operator::Semicolon => Associativity::Right,
      _ => Associativity::Left,
    }
  }

  fn precedence(&self) -> u8 {
    match self {
      Operator::ParenthesisLeft | Operator::ParenthesisRight => 1,
      Operator::SquareBracketLeft | Operator::SquareBracketRight => 1,
      // Operator::CurlyBraketLeft | Operator::CurlyBraketRight => 1,
      Operator::Semicolon => 2,
      Operator::Assign => 3,
      Operator::Equal | Operator::NotEqual => 4,
      Operator::Lesser | Operator::Greater | Operator::LesserEqual | Operator::GreaterEqual => 5,
      Operator::Add | Operator::Subtract => 6,
      Operator::Multiply | Operator::Divide | Operator::FloorDivide => 7,
      _ => panic!("Operator {} has no precedence", self),
    }
  }
}

// A token is a part in which inserting whitespace changes its meaning.
#[derive(Display, Debug)]
enum Token {
  VariableName(VariableName),
  Operator(Operator),
  Constant(Variable),
}

#[derive(Debug, Clone)]
enum OperatorTree {
  VariableName(VariableName),
  Literal(Variable),
  OperatorTree(Operator, Vec<OperatorTree>),
}

fn main() {
  let file_path = match env::args().nth(2) {
    Some(path) => path,
    None => "../examples/find_max.ptls".to_string(),
  };
  let content = fs::read_to_string(file_path).unwrap();
  // println!("content: {}", content);
  let inital_command = pre_compile(&content);
  // println!("inital_command: {}", inital_command);
  let mut variables: HashMap<VariableName, Variable> = HashMap::new();
  execute(&inital_command, &mut variables);
  // println!("HashMap: {:?}", variables);
  fn print_list(list: Vec<Variable>) {
    for item in list {
      match item {
        Variable::Number(num) => {
          print!("{}", num);
        }
        Variable::String(string) => {
          print!("{}", string);
        }
        Variable::List(list) => {
          print_list(list);
        }
        Variable::None => {}
      }
    }
  }
  loop {
    let cmd = match variables.remove("cmd") {
      Some(Variable::List(mut cmds)) => {
        if cmds.is_empty() {
          break;
        }
        let cmd = cmds.remove(0);
        variables.insert("cmd".to_string(), Variable::List(cmds));
        cmd
      }
      _ => break,
    };
    match cmd {
      Variable::String(cmd) => {
        execute(&cmd, &mut variables);
      }
      Variable::Number(num) => {
        print!("{}", num);
      }
      Variable::List(list) => {
        print_list(list);
      }
      _ => {}
    }
  }
}

fn pre_compile(content: &str) -> Command {
  let mut cmd = String::new();
  let mut char_iter = content.chars().peekable();
  while let Some(c) = char_iter.next() {
    match c {
      '#' => {
        while let Some(c) = char_iter.next() {
          if c == '\n' {
            cmd.push(c);
            break;
          }
        }
      }
      '\'' | '"' => {
        cmd.push(c);
        while let Some(d) = char_iter.next() {
          cmd.push(d);
          if c == d {
            break;
          }
          if d == '\\' {
            if let Some(e) = char_iter.peek() {
              match e {
                'n' | 't' | '\'' | '"' | '\\' => {
                  cmd.push(char_iter.next().unwrap());
                }
                _ => {}
              }
            }
          }
        }
      }
      _ => {
        cmd.push(c);
      }
    }
  }
  format!("cmd = {{{}}}", cmd)
}

fn execute(command: &str, variables: &mut HashMap<String, Variable>) {
  // println!("Executing command: {}", command);
  let tokens = tokenize(command);
  // println!("tokens: {:?}", tokens);
  let operator_tree = generate_operator_tree(tokens);
  // println!("operator_tree: {:?}", operator_tree);
  calculate_operator_tree(operator_tree, variables);
  // println!("Variables: {:?}", variables);
}

fn tokenize(content: &str) -> Vec<Token> {
  let mut tokens = Vec::new();
  let mut char_iter = content.chars().peekable();
  while let Some(c) = char_iter.next() {
    match c {
      'a'..='z' | 'A'..='Z' | '_' => {
        let mut name = String::new();
        name.push(c);
        while let Some(d) = char_iter.peek() {
          if d.is_alphanumeric() || *d == '_' {
            name.push(char_iter.next().unwrap());
          } else {
            break;
          }
        }
        tokens.push(Token::VariableName(name));
      }
      '0'..='9' => {
        let mut value = c.to_digit(10).unwrap() as Number;
        let mut weight = 1 as Number;
        while let Some(d) = char_iter.peek() {
          if let Some(digit) = d.to_digit(10) {
            char_iter.next();
            if weight == 1.0 {
              value = value * 10.0 + digit as Number;
            } else {
              value = value + digit as Number * weight;
              weight *= 0.1;
            }
          } else if c == '.' {
            char_iter.next();
            if weight == 1.0 {
              weight *= 0.1;
            } else {
              panic!("More than one decimal point in number")
            }
          } else {
            break;
          }
        }
        tokens.push(Token::Constant(Variable::Number(value)));
      }
      '\'' | '"' => {
        let mut value = String::new();
        while let Some(d) = char_iter.next() {
          if d == c {
            break;
          }
          if d == '\\' {
            if let Some(e) = char_iter.peek() {
              match e {
                'n' => {
                  value.push('\n');
                  char_iter.next();
                }
                // 't' => {
                //     value.push('\t');
                //     char_iter.next();
                // }
                '\'' | '"' | '\\' => {
                  value.push(char_iter.next().unwrap());
                }
                _ => {}
              }
            }
          } else {
            value.push(d);
          }
        }
        tokens.push(Token::Constant(Variable::String(value)));
      }
      '{' => {
        let mut left_brackets = vec![Operator::CurlyBraketLeft];
        let mut list = Vec::<Variable>::new();
        let mut buffer = String::new();
        while let Some(d) = char_iter.next() {
          match d {
            '{' => {
              left_brackets.push(Operator::CurlyBraketLeft);
              buffer.push(d);
            }
            '}' => {
              let top = left_brackets.pop().unwrap();
              assert_eq!(top, Operator::CurlyBraketLeft);
              if left_brackets.len() > 0 {
                buffer.push(d);
              } else {
                list.push(Variable::String(buffer));
                break;
              }
            }
            '[' => {
              left_brackets.push(Operator::SquareBracketLeft);
              buffer.push(d);
            }
            ']' => {
              let top = left_brackets.pop().unwrap();
              assert_eq!(top, Operator::SquareBracketLeft);
              buffer.push(d);
            }
            ';' if left_brackets.len() == 1 => {
              list.push(Variable::String(buffer));
              buffer = String::new();
            }
            ';' if left_brackets.len() != 1 => {
              buffer.push(d);
            }
            _ => {
              buffer.push(d);
            }
          }
        }
        tokens.push(Token::Constant(Variable::List(list)));
      }
      _ => {
        let mut op = Operator::None;
        if let Some(d) = char_iter.peek() {
          op = Operator::from(format!("{}{}", c, d).as_str());
        }
        if op != Operator::None {
          char_iter.next();
        } else {
          op = Operator::from(c.to_string().as_str());
        }
        if op != Operator::None {
          tokens.push(Token::Operator(op));
        } else if c.is_whitespace() {
          // println!("Skipping whitespace: {}", c);
        } else {
          panic!("Invalid character: {}", c);
        }
      }
    }
  }
  tokens
}

fn generate_operator_tree(tokens: Vec<Token>) -> OperatorTree {
  if tokens.is_empty() {
    return OperatorTree::Literal(Variable::None);
  }
  #[derive(Clone, Debug)]
  enum ElementType {
    Variable(OperatorTree),
    Operator(Operator),
  }
  let mut stack = Vec::<ElementType>::new();
  fn use_operator(stack: &mut Vec<ElementType>) -> Result<(), ()> {
    let right = match stack.pop().unwrap() {
      ElementType::Variable(v) => v,
      _ => panic!("Stack top should be variable"),
    };
    let op = match stack.pop().unwrap() {
      ElementType::Operator(o) => o,
      _ => panic!("Stack top should be operator"),
    };
    let left = match stack.pop().unwrap() {
      ElementType::Variable(v) => v,
      _ => panic!("Stack top should be variable"),
    };
    stack.push(ElementType::Variable(OperatorTree::OperatorTree(
      op,
      vec![left, right],
    )));
    // println!("stack top: {:?}", stack.last().unwrap());
    Ok(())
  }
  fn merge_expression(stack: &mut Vec<ElementType>, prece: &Operator) {
    while stack.len() > 2 {
      // println!("stack: {:?}, prece: {}", stack, prece);
      // &stack[stack.len() - 2] is the second to last element in the stack
      if let ElementType::Operator(top_op) = &stack[stack.len() - 2] {
        // println!("top_op: {}", top_op);
        if top_op.precedence() > prece.precedence()
          || (top_op.precedence() == prece.precedence()
            && top_op.associativity() == Associativity::Left)
        {
          let _ = use_operator(stack);
          continue;
        }
      }
      // println!("break");
      break;
    }
  }
  for token in tokens {
    match token {
      Token::VariableName(name) => {
        stack.push(ElementType::Variable(OperatorTree::VariableName(name)));
      }
      Token::Constant(constant) => {
        stack.push(ElementType::Variable(OperatorTree::Literal(constant)));
      }
      Token::Operator(op) => match op {
        Operator::Add
        | Operator::Subtract
        | Operator::Multiply
        | Operator::Divide
        | Operator::FloorDivide
        | Operator::Lesser
        | Operator::Greater
        | Operator::LesserEqual
        | Operator::GreaterEqual
        | Operator::Equal
        | Operator::NotEqual
        | Operator::Assign
        | Operator::Semicolon => {
          merge_expression(&mut stack, &op);
          stack.push(ElementType::Operator(op));
        }
        Operator::ParenthesisLeft | Operator::SquareBracketLeft => {
          stack.push(ElementType::Operator(op));
        }
        Operator::ParenthesisRight => {
          merge_expression(&mut stack, &Operator::ParenthesisLeft);
          if let ElementType::Variable(var) = stack.pop().unwrap() {
            if let ElementType::Operator(Operator::ParenthesisLeft) = stack.pop().unwrap() {
            } else {
              panic!("Compiler error: expected parenthesis left")
            }
            stack.push(ElementType::Variable(var));
          }
        }
        Operator::SquareBracketRight => {
          merge_expression(&mut stack, &Operator::Semicolon);
          stack.push(ElementType::Operator(Operator::Semicolon));
          let mut buffer = Vec::<OperatorTree>::new();
          while stack.len() > 0 {
            if let ElementType::Operator(op) = stack.pop().unwrap() {
              if op == Operator::SquareBracketLeft {
                break;
              }
              assert_eq!(
                op,
                Operator::Semicolon,
                "Compiler error: expected semicolon"
              );
              if let ElementType::Variable(var) = stack.pop().unwrap() {
                buffer.push(var);
              } else {
                panic!("Stack top should be variable");
              }
            } else {
              panic!("Stack top should be operator");
            }
          }
          buffer.reverse();
          if let ElementType::Variable(var) = stack.last().unwrap().to_owned() {
            assert_eq!(buffer.len(), 1, "Compiler error: expected one variable");
            stack.pop();
            stack.push(ElementType::Variable(OperatorTree::OperatorTree(
              Operator::Get,
              vec![var, buffer.remove(0)],
            )));
          } else {
            stack.push(ElementType::Variable(OperatorTree::OperatorTree(
              Operator::CreateList,
              buffer,
            )));
          }
        }
        _ => {
          panic!("Unsupported operator: {}", op)
        }
      },
    }
  }
  merge_expression(&mut stack, &Operator::ParenthesisLeft);
  // println!("stack: {:?}", stack);
  assert_eq!(
    stack.len(),
    1,
    "Compiler error: stack should have one element"
  );
  if let ElementType::Variable(t) = stack.remove(0) {
    t
  } else {
    panic!("Compiler error: element type should be variable")
  }
}

fn calculate_operator_tree<'a>(
  operator_tree: OperatorTree,
  variables: &'a mut HashMap<String, Variable>,
) -> Either<&'a mut Variable, Variable> {
  fn to_right_value(value: Either<&mut Variable, Variable>) -> Variable {
    match value {
      Either::Left(var) => var.to_owned(),
      Either::Right(var) => var,
    }
  }
  match operator_tree {
    OperatorTree::VariableName(name) => {
      Either::Left(variables.entry(name.clone()).or_insert(Variable::None))
    }
    OperatorTree::Literal(constant) => Either::Right(constant),
    OperatorTree::OperatorTree(op, mut operands) => match op {
      Operator::Add => {
        assert_eq!(
          operands.len(),
          2,
          "Compiler error: {} has {} operands",
          op,
          operands.len()
        );
        operands.reverse();
        // println!("operands: {:?}", operands);
        let mut get_value = || {
          if operands.len() > 0 {
            Some(to_right_value(calculate_operator_tree(
              operands.pop().unwrap(),
              variables,
            )))
          } else {
            None
          }
        };
        let first_value = get_value().unwrap();
        match first_value {
          Variable::Number(mut result) => {
            if let Some(Variable::Number(value)) = get_value() {
              result += value;
            }
            assert!(
              operands.is_empty(),
              "Compiler error: error operands for operator {}",
              op
            );
            Either::Right(Variable::Number(result))
          }
          Variable::String(mut result) => {
            if let Some(Variable::String(value)) = get_value() {
              result.push_str(&value);
            }
            assert!(
              operands.is_empty(),
              "Compiler error: error operands for operator {}",
              op
            );
            Either::Right(Variable::String(result))
          }
          Variable::List(mut result) => {
            while let Some(Variable::List(value)) = get_value() {
              result.extend(value);
            }
            assert!(
              operands.is_empty(),
              "Compiler error: error operands for operator {}",
              op
            );
            Either::Right(Variable::List(result))
          }
          _ => panic!(
            "Compiler error: {} right value should be number or string or list",
            op
          ),
        }
      }
      Operator::Subtract
      | Operator::Multiply
      | Operator::Divide
      | Operator::FloorDivide
      | Operator::Lesser
      | Operator::Greater
      | Operator::LesserEqual
      | Operator::GreaterEqual
      | Operator::Equal
      | Operator::NotEqual => {
        let left = match to_right_value(calculate_operator_tree(operands.remove(0), variables)) {
          Variable::Number(left) => left,
          _ => panic!("Compiler error: {} left value should be number", op),
        };
        let right = match to_right_value(calculate_operator_tree(operands.remove(0), variables)) {
          Variable::Number(right) => right,
          _ => panic!("Compiler error: {} right value should be number", op),
        };
        match op {
          Operator::Subtract => Either::Right(Variable::Number(left - right)),
          Operator::Multiply => Either::Right(Variable::Number(left * right)),
          Operator::Divide => Either::Right(Variable::Number(left / right)),
          Operator::FloorDivide => Either::Right(Variable::Number((left / right).floor())),
          Operator::Lesser => Either::Right(Variable::Number(if left < right { 1.0 } else { 0.0 })),
          Operator::Greater => {
            Either::Right(Variable::Number(if left > right { 1.0 } else { 0.0 }))
          }
          Operator::LesserEqual => {
            Either::Right(Variable::Number(if left <= right { 1.0 } else { 0.0 }))
          }
          Operator::GreaterEqual => {
            Either::Right(Variable::Number(if left >= right { 1.0 } else { 0.0 }))
          }
          Operator::Equal => Either::Right(Variable::Number(if left == right { 1.0 } else { 0.0 })),
          Operator::NotEqual => {
            Either::Right(Variable::Number(if left != right { 1.0 } else { 0.0 }))
          }
          _ => unreachable!(),
        }
      }
      Operator::Assign => {
        let right_value = to_right_value(calculate_operator_tree(operands.remove(1), variables));
        if let Either::Left(left_value) = calculate_operator_tree(operands.remove(0), variables) {
          *left_value = right_value;
          Either::Left(left_value)
        } else {
          panic!("Compiler error: left value should not be literal")
        }
      }
      Operator::Get => {
        let right = to_right_value(calculate_operator_tree(operands.remove(1), variables));
        if let Variable::Number(index) = right {
          let index = index as usize;
          let left = calculate_operator_tree(operands.remove(0), variables);
          if let Either::Left(Variable::List(list)) = left {
            if index < list.len() {
              Either::Left(list.index_mut(index))
            } else {
              panic!("Compiler error: index out of range")
            }
          } else if let Either::Right(Variable::List(list)) = left {
            if index < list.len() {
              Either::Right(list[index].clone())
            } else {
              panic!("Compiler error: index out of range")
            }
          } else if let Either::Left(Variable::String(string)) = left {
            if index < string.len() {
              Either::Right(Variable::String(
                string.chars().nth(index).unwrap().to_string(),
              ))
            } else {
              panic!("Compiler error: index out of range")
            }
          } else if let Either::Right(Variable::String(string)) = left {
            if index < string.len() {
              Either::Right(Variable::String(
                string.chars().nth(index).unwrap().to_string(),
              ))
            } else {
              panic!("Compiler error: index out of range")
            }
          } else {
            panic!("Compiler error: left value should be list or string")
          }
        } else {
          panic!("Compiler error: index should be number")
        }
      }
      Operator::CreateList => {
        let mut list = Vec::<Variable>::new();
        for operand in operands {
          list.push(to_right_value(calculate_operator_tree(operand, variables)));
        }
        Either::Right(Variable::List(list))
      }
      _ => {
        panic!("Operator {} should not be calculated", op)
      }
    },
  }
}
