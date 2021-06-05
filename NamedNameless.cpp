#include <iostream>
#include <string>
#include <map>
#include <stack>

std::string deBrujnToLambda(std::string term) {
	std::map<int, std::string> numsToVars;
	std::string newTerm = "";
	std::stack<char> applicationsAndLambdas;
	int currVarNum = 0;
	int lambdaCounter = 0;
	for (int i = 0; i < term.size(); i++) {
		char curr = term[i];
		if (curr == '(') {
			newTerm.append("(");
			applicationsAndLambdas.push('b'); //b stands for bracket, we are not sure of its purpose for now
		}
		else if (curr == ')') {
			newTerm.append(")");
			if (!applicationsAndLambdas.empty()) {
				if (applicationsAndLambdas.top() == 'l') {
					lambdaCounter--;
				}
				applicationsAndLambdas.pop();
			}
		}
		else if (curr == '\\') {
			lambdaCounter++;
			newTerm.append("\\");
			if (!applicationsAndLambdas.empty() && applicationsAndLambdas.top() == 'b') {
				applicationsAndLambdas.pop();
			}
			applicationsAndLambdas.push('l');
			std::string currVar = "x" + std::to_string(currVarNum++);
			numsToVars[(-1) * lambdaCounter] = currVar;
			newTerm.append("'" + currVar + "'");
		}
		else {
			int num = curr - '0' - lambdaCounter;
			if (numsToVars.find(num) == numsToVars.end()) {
				numsToVars[num] = "x" + std::to_string(currVarNum++);
			}
			newTerm.append("'" + numsToVars[num] + "'");
		}
	}
	return newTerm;
}

std::string getVar(std::string term, int pos){
	std::string name = "";
	while (term[pos] != '\'') {
		name += term[pos];
		pos++;
	}
	return name;
}

std::string lambdaToDeBrujn(std::string term) {
	std::string newTerm = "";
	std::map<std::string, int> varsToNums;
	int lambdaCounter = 0;
	int freeVarsCounter = 0;
	std::stack<char> applicationsAndLambdas;
	for (int i = 0; i < term.size(); i++) {
		char curr = term[i];
		if (curr == '(') {
			newTerm.append("(");
			applicationsAndLambdas.push('b'); //b stands for bracket, we are not sure of its purpose for now
		}
		else if (curr == ')') {
			newTerm.append(")");
			if (!applicationsAndLambdas.empty()) {
				if (applicationsAndLambdas.top() == 'l') {
					lambdaCounter--;
				}
				applicationsAndLambdas.pop();
			}
		}
		else if (curr == '\\') {
			lambdaCounter++;
			newTerm.append("\\");
			if (!applicationsAndLambdas.empty() && applicationsAndLambdas.top() == 'b') {
				applicationsAndLambdas.pop();
			}
			applicationsAndLambdas.push('l');

			//get the var name, starts seaching from the first position in the actual var name
			std::string varName = getVar(term, i + 2);
			i += 2 + varName.size(); // 3 is because we want to skip \'' too

			//bounded variable
			varsToNums[varName] = -lambdaCounter;
		}
		else {
			//the only other option we is ' as we will skip all letters when getting var names
			std::string varName = getVar(term, i + 1);
			i += 1 + varName.size();

			if (varsToNums.find(varName) == varsToNums.end()) {
				//first time seeing the current variable and not in lambda -> free variable
				varsToNums[varName] = freeVarsCounter++;
			}

			newTerm.append(std::to_string(varsToNums[varName] + lambdaCounter));
		}
	}
	return newTerm;
}

//Format: \ for lambda, named vars names should be surrounded by ''

int main() {
	std::string term;
	char dir;
	std::cout << "For deBrujn to lambda press a, else press b: ";
	std::cin >> dir;
	std::cout << "Please insert the lambda term: ";
	std::cin >> term;
	std::string newTerm;
	if (dir == 'a') {
		newTerm = deBrujnToLambda(term);
	}
	else if (dir == 'b') {
		newTerm = lambdaToDeBrujn(term);
	}
	else {
		std::cout << "Invalid input\n";
		return 0;
	}
	std::cout << newTerm << std::endl;
	return 0;
}