/* 
* Written By Brandon Knudson and Tristan Hedrick
* COP3402 
* Fall 2022
*/
#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include "compiler.h"
// Global Array's w/ Indices
lexeme *tokens;
int token_index = 0;
symbol *table;
int table_index = 0;
instruction *code;
int code_index = 0;
// Other Variables
int error = 0;
int level;
// Given Functions
void emit(int op, int l, int m);
void add_symbol(int kind, char name[], int value, int level, int address);
void mark();
int multiple_declaration_check(char name[]);
int find_symbol(char name[], int kind);
// Additional Functions for each Non-Terminal Symbol
void block(); 		// B.K.
void declarations();// B.K.
void constants(); 	// B.K.
void procedures();	// B.K.
void variables(int var_count);	// B.K.
void statement(); 	// T.H.
void term();		// T.H.
void factor();		// T.H.
void condition();	// T.H.
void expression();	// T.H.
// Print Functions
void print_parser_error(int error_code, int case_code);
void print_assembly_code();
void print_symbol_table();

instruction *parse(int code_flag, int table_flag, lexeme *list) // B.K.
{
	// Variable Initialization
	tokens = list;
	table = calloc(ARRAY_SIZE, sizeof(symbol));
	code = calloc(ARRAY_SIZE, sizeof(instruction));
	level = -1;
	// Main Procedure Block Recursive Call
	block();
	// If no stopping error finish program parsing
	if (error != -1) {
		if (tokens[token_index].type != period) {
			print_parser_error(1,0);
			error = 1;
		}
		// Search generated assembly code for each CAL and check if m is set to address
		for (int i = 0; i < code_index ; i++) {
			if (code[i].op == CAL && code[i].m != -1)  { // If CALL procedure is defined in instruction and m is set to something
				if (table[code[i].m].address == -1) { // If Symbol table doesn't have address
					print_parser_error(21,0);
					error = 1;
				}
				else { // If the procedure has an address, set the m for CALL to this location
					code[i].m = table[code[i].m].address;
				}
			}
		} // If there is code to end the program block add it to code
		if (code[code_index].op != GEQ || code[code_index].op != LOD) {
			emit(GEQ,0,3);
		}
		// Print if Flags are set
		if (error == 0) {
			if (code_flag != 0) {
				print_assembly_code();
			}
			if (table_flag != 0) {
				print_symbol_table();
			}
			free(table);
		}
		// If there is an error at the end set code to null
		else {
			free(table);
			free(code);
			code == NULL;
		}
		// will return code if no errors otherwise null
		return code;
	}
	// If there is an error somewhere in the program block return null
	free(table);
	free(code);
	return NULL;
}

void statement() {
	int temp_level,temp_address;
	int temp_code_index1 = code_index;
	int temp_table_index;
    switch (tokens[token_index].type) {
		case identifier:
			if (find_symbol(tokens[token_index].identifier_name, 2) == -1) {
				if (find_symbol(tokens[token_index].identifier_name, 1) == find_symbol(tokens[token_index].identifier_name, 2)) {
					print_parser_error(8,1);
				}
				else {
					print_parser_error(7,0);
					error = 1;
				}
			}
			else {
			// Cache Current Level and Address
			temp_level = level - table[find_symbol(tokens[token_index].identifier_name, 2)].level;
			temp_address = table[find_symbol(tokens[token_index].identifier_name, 2)].address;
			}
			if (tokens[token_index + 1].type == assignment_symbol) {
			token_index += 2; // Assignment symbol is 2 chars long
			}
			else {
			token_index++;
			print_parser_error(4,2);
			if (tokens[token_index].type != identifier && tokens[token_index].type != number && tokens[token_index].type != left_parenthesis) { 
				error = -1;
				return;
			}
			error = 1;
			}
			expression();
			if (error != -1) {
			emit(STO, temp_level, temp_address); // STO L,M
			}
			break;
		case keyword_call:
			token_index++;
			if (tokens[token_index].type == identifier) {
				if (find_symbol(tokens[token_index].identifier_name, 3) == -1) {
					if (find_symbol(tokens[token_index].identifier_name, 1) == find_symbol(tokens[token_index].identifier_name, 2)) {
						print_parser_error(8,2);
					}
					else {
						print_parser_error(9,0);
					}
					error = 1;
				}
				else {
					temp_level = level - table[find_symbol(tokens[token_index].identifier_name, 2)].level;
					temp_address = table[find_symbol(tokens[token_index].identifier_name, 2)].address;
				}
				token_index++;
			}
			else {
				print_parser_error(2, 4);
				if (tokens[token_index].type != period && tokens[token_index].type != right_curly_brace && tokens[token_index].type != semicolon && 
					tokens[token_index].type != keyword_end) {
					error = -1;
					return;
				}
				error = 1;
			} 
			emit(CAL, temp_level, temp_address); // CAL L,M
			break;
		case keyword_begin:
			do {
				token_index++;
				statement();
				if (error == -1) {
					return;
				}
			} while (tokens[token_index].type == keyword_write );
			if (tokens[token_index].type == keyword_end) {
				token_index++;
			}
			else {
				if (tokens[token_index].type == identifier || tokens[token_index].type == keyword_call ||
					tokens[token_index].type == keyword_begin || tokens[token_index].type == keyword_if || tokens[token_index].type == keyword_while ||
					tokens[token_index].type == keyword_read || tokens[token_index].type == keyword_write || tokens[token_index].type == keyword_def ||
					tokens[token_index].type == keyword_return
				) {
					print_parser_error(6,4);
					error = -1;
				}
				else {
					print_parser_error(10,0);
					if (tokens[token_index].type == period || tokens[token_index].type ==right_curly_brace || tokens[token_index].type == semicolon) {
						error = 1;
					}
					else {
						error = -1;
					}
				}
			}
			break;
		case keyword_if:
			token_index++;
			condition();
			temp_code_index1 = code_index;
			if (error != -1) {
				emit(GTR,0,0);
				if (tokens[token_index].type == keyword_then) {
					token_index++;
				}
				else {
					print_parser_error(11,0);
					if (tokens[token_index].type != identifier && tokens[token_index].type != keyword_call && tokens[token_index].type != keyword_begin &&
					tokens[token_index].type != keyword_if && tokens[token_index].type != keyword_while && tokens[token_index].type != keyword_read &&
					tokens[token_index].type != keyword_write && tokens[token_index].type != keyword_def &&
					tokens[token_index].type != keyword_return && tokens[token_index].type != keyword_end && tokens[token_index].type != period && 
					tokens[token_index].type != right_curly_brace && tokens[token_index].type != semicolon) {
						error = -1;
						return;
					}
					error = 1;
				}
				statement();
				if (error != -1) {
					code[temp_code_index1].l = code_index; // stores level from before recursive statement call to new code_index after recursive call
				}
			}
			break;
		case keyword_while:
			token_index++;
			condition();
			int temp_code_index2 = code_index;
			if (error != -1) {
				emit(GTR,0,0);
				if (tokens[token_index].type == keyword_do) {
					token_index++;
				}
				else {
					print_parser_error(12,0);
					if (tokens[token_index].type != identifier && tokens[token_index].type != keyword_call && tokens[token_index].type != keyword_begin &&
					tokens[token_index].type != keyword_if && tokens[token_index].type != keyword_while && tokens[token_index].type != keyword_read && 
					tokens[token_index].type != keyword_write && tokens[token_index].type != keyword_def && tokens[token_index].type != keyword_return && 
					tokens[token_index].type != period && tokens[token_index].type != right_curly_brace && tokens[token_index].type != semicolon && 
					tokens[token_index].type != keyword_end
					) {
						error = -1;
						return;
					}
					error = 1;
				}
				statement();
				if  (error != -1) {
					emit(LEQ,0,temp_code_index1); // Memory address will be beginning of statement
					code[temp_code_index2].m = code_index; // Store current address in m from before recursive call
				}
			}
			break;
		case keyword_read:
			token_index++;
			if (tokens[token_index].type == identifier) {
				if (find_symbol(tokens[token_index].identifier_name, 2) == -1) {
					if (find_symbol(tokens[token_index].identifier_name, 1) == find_symbol(tokens[token_index].identifier_name, 3)) {
						print_parser_error(8,3);
					}
					else {
						print_parser_error(13,0);
					}
					error = 1;
				}
				else {
					temp_level = level - table[find_symbol(tokens[token_index].identifier_name, 2)].level;
					temp_address = table[find_symbol(tokens[token_index].identifier_name, 2)].address;
				}
			token_index++;
			}
			else {
				print_parser_error(2,5);
				if (tokens[token_index].type != period && tokens[token_index].type != right_curly_brace && tokens[token_index].type != semicolon && 
					tokens[token_index].type != keyword_end) {
					error = -1;
					return;
				}
			error = 1;
			}
			emit(GEQ,0,2); // GEQ L,M
			emit(STO,temp_level,temp_address); // STO L,M
			break;
		case keyword_write:
			token_index++;
			expression();
			if (error != -1) {
				emit(GEQ,0,1);
			}
			break;
		case keyword_return:
			if (level == 0) {
				emit(GEQ,0,3);
			}
			else {
				emit(NEQ,0,0);
			}
			token_index++;
			break;
		case keyword_def:
			token_index++;
			if (tokens[token_index].type == identifier) {
				temp_table_index = find_symbol(tokens[token_index].identifier_name,3);
				if (temp_table_index == -1) {
					if (find_symbol(tokens[token_index].identifier_name,1) == find_symbol(tokens[token_index].identifier_name,2)) {
						print_parser_error(8,4);
					}
					else {
						print_parser_error(14,0);
					}
					error = 1;
				}
				else if (table[temp_table_index].level == level) {
					if (table[temp_table_index].address != -1) {
						print_parser_error(23,0);
						error = 1;
						temp_table_index = -1;
					}
				}
				else {
					print_parser_error(22,0);
					error = 1;
					temp_table_index = -1;
				}
				token_index++;
			}
			else {
				print_parser_error(2,6);
				if(tokens[token_index].type != left_curly_brace) {
					error = -1;
					return;
				}
				error = 1;
				temp_table_index = -1;
			}
			if (tokens[token_index].type == left_curly_brace) {
				token_index++;
			}
			else {
				print_parser_error(15,0);
				if (tokens[token_index].type != keyword_const && tokens[token_index].type != keyword_var && tokens[token_index].type != keyword_procedure &&
					tokens[token_index].type != identifier && tokens[token_index].type != keyword_call && tokens[token_index].type != keyword_begin && 
					tokens[token_index].type != keyword_if && tokens[token_index].type != keyword_while && tokens[token_index].type != keyword_read &&
					tokens[token_index].type != keyword_write && tokens[token_index].type != keyword_def && tokens[token_index].type != keyword_return && 
					tokens[token_index].type != right_curly_brace
					) {
						error = -1;
						return;
					}
				error = 1;
			}
			temp_code_index1 = code_index;
			emit(LEQ,0,0);
			if(temp_table_index != -1) {
				table[temp_table_index].address = code_index;
			}
			block();
			if (error != -1) {
				if (code[code_index].op != NEQ) { //.OP?
					emit(NEQ,0,0);
				}
				code[temp_code_index1].m = code_index;
				if (tokens[token_index].type == right_curly_brace) {
					token_index++;
				}
				else {
					print_parser_error(16,0);
					if (tokens[token_index].type == semicolon || tokens[token_index].type == period || tokens[token_index].type == keyword_end) {
						error = 1;
					}
					else {
						error = -1;
					}
				}
			}
		}
    return;
}

void condition() { 
	expression();
  	if (error != -1) {
		int temp_token_type = tokens[token_index].type;
    	if (temp_token_type == equal_to || temp_token_type == not_equal_to || 
        	temp_token_type == less_than || temp_token_type == less_than_or_equal_to || 
        	temp_token_type == greater_than || temp_token_type == greater_than_or_equal_to)
		{
      		token_index++;
    	}
    	else {
    		print_parser_error(17,0);
      		if (temp_token_type != identifier && temp_token_type != number && temp_token_type != left_parenthesis) {
    			error = -1;
        		return;
      		}
    		error = 1;
    	}
    	expression();
    	if (error != -1) {
			switch(temp_token_type) {
				case equal_to:
					emit(OPR,0,5);
					break;
				case not_equal_to:
					emit(OPR,0,6);
					break;
				case less_than:
					emit(OPR,0,7);
					break;
				case less_than_or_equal_to:
					emit(OPR,0,8);
					break;
				case greater_than:
					emit(OPR,0,9);
					break;
				case greater_than_or_equal_to:
					emit(OPR,0,10);
					break;
				default:
					emit(OPR,0,-1);
      		}
    	}
  	}
  return;
}

void expression() {
	int temp_token; // Cached Token Type Value As We Will Need to Store Previous type for +|- logic
	term(); // Starts with a term
	if (error != -1) {
    	while (temp_token == plus || temp_token == minus) { // Then +|- Term 0 or more times
			token_index++;
      		term();
      		if (error == -1) {
        		return;
      		}
      		if (temp_token == plus) {
        		emit(OPR,0,1);
      		}
      		else {
        		emit(OPR,0,2);
      		}
      		temp_token = tokens[token_index].type;
    	}
  	}
  return;
}
void term() {
	int temp_token; // Cached Token Type Value As We Will Need to Store Previous type for *|/ logic
  	factor(); // Starts with a Factor
  	if (error != -1) {
    	temp_token = tokens[token_index].type;
    	while (temp_token == times ||  temp_token == division) { // "*|/ Factor" repeated 0 or more times)
      		token_index++;
      		factor();
      		if (error == -1) {
        		return;
      		}
      		if ( temp_token == times) {
        		emit(OPR,0,3);
      		}
      		else {
        		emit(OPR,0,4);
      		}
    		temp_token = tokens[token_index].type;
    	}
  	}
	return;
}
void factor() {  
	if (tokens[token_index].type == identifier) {
    	if (find_symbol(tokens[token_index].identifier_name,1) == find_symbol(tokens[token_index].identifier_name,2)) {
      		if (find_symbol(tokens[token_index].identifier_name,3) == -1) {
        		print_parser_error(8,5);
      		}
     		else {
        		print_parser_error(18,0);
      		}
      		error = 1;
      		emit(LOD,-1,-1);
    	}
   		else if (find_symbol(tokens[token_index].identifier_name,1) == -1) {
      		emit(LOD,level - table[find_symbol(tokens[token_index].identifier_name,2)].level, table[find_symbol(tokens[token_index].identifier_name,2)].address);
    	}
    	else if (find_symbol(tokens[token_index].identifier_name,2) == -1) {
      		emit(LOD,0,table[find_symbol(tokens[token_index].identifier_name,1)].value); // Value? Maybe address?
    	}
    	else if (table[find_symbol(tokens[token_index].identifier_name,2)].level < table[find_symbol(tokens[token_index].identifier_name,1)].level) {
      		emit(LOD,0,table[find_symbol(tokens[token_index].identifier_name,1)].value);
    	}
    	else {
      		emit(LOD,level - table[find_symbol(tokens[token_index].identifier_name,2)].level,table[find_symbol(tokens[token_index].identifier_name,2)].address);
   		}
    	token_index++;
  	}
  	else if (tokens[token_index].type == number) {
    	emit(LIT,0, tokens[token_index].number_value); // Number Value?
    	token_index++;
  	}
  	else if (tokens[token_index].type == left_parenthesis) {
		token_index++;
		expression();
		if (error != -1) {
			if (tokens[token_index].type == right_parenthesis) {
				token_index++;
			}
			else {
				print_parser_error(19,0);
				if (tokens[token_index].type == period || tokens[token_index].type == right_curly_brace || tokens[token_index].type == semicolon ||
					tokens[token_index].type == keyword_end || tokens[token_index].type == equal_to || tokens[token_index].type == division || 
					tokens[token_index].type == not_equal_to || tokens[token_index].type == less_than || tokens[token_index].type == less_than_or_equal_to ||
					tokens[token_index].type == greater_than || tokens[token_index].type == greater_than_or_equal_to || 
					tokens[token_index].type == keyword_then || tokens[token_index].type == keyword_do || 
					tokens[token_index].type == plus || tokens[token_index].type == minus || tokens[token_index].type == times
				) {
					error = 1;
				}
				else {
					error = -1;
				}
			}
		}
  	}
	else {
		print_parser_error(20,0);
		tokens[token_index].type = tokens[token_index].type;
		if (tokens[token_index].type == right_parenthesis || tokens[token_index].type == period || tokens[token_index].type == right_curly_brace ||
			tokens[token_index].type == semicolon || tokens[token_index].type == keyword_end || tokens[token_index].type == division || 
			tokens[token_index].type == equal_to || tokens[token_index].type == not_equal_to || tokens[token_index].type == less_than ||
			tokens[token_index].type == less_than_or_equal_to || tokens[token_index].type == greater_than || 
			tokens[token_index].type == greater_than_or_equal_to || tokens[token_index].type == keyword_then || tokens[token_index].type == keyword_do || 
			tokens[token_index].type == plus || tokens[token_index].type == minus || tokens[token_index].type == times
		) {
			error = 1;
		}
		else {
		error = -1;
		}
  	}
  return;
}
// large if-else statement used in constants and procedures
int special_error_check() {
	int tempTypeNum = tokens[token_index].type;
		// Non-stopping error
		if (tempTypeNum==1||tempTypeNum==3||tempTypeNum==4||tempTypeNum==5||tempTypeNum==6||tempTypeNum==7||tempTypeNum==9||tempTypeNum==11||tempTypeNum== 13||tempTypeNum==14||tempTypeNum==15||tempTypeNum==16||tempTypeNum==17||tempTypeNum==22) {
			error = 1;
		}
		// Stopping Error
		else {
			error = -1;
		}
}

void procedures() {
	char * temp;
	// Check for identifier and if the name is valid
	token_index++;
	if (tokens[token_index].type == identifier) {
		if (multiple_declaration_check(tokens[token_index].identifier_name) != -1) {
			print_parser_error(3,0);
			error =1;
		}
		// Save Identifier Name for Later
		temp = tokens[token_index].identifier_name;
		token_index++;
	}
	else {
		print_parser_error(2,3);
		if (tokens[token_index].type != semicolon) {
			error = -1;
			return;
		}
		error = 1;
		temp = NULL;
	}
	add_symbol(LOD, temp, 0, level, -1);
	if (tokens[token_index].type == semicolon) {
		token_index++;
	}
	// If semi colon is missing check for stopping or non stopping error
	else {
		print_parser_error(6,3);
		special_error_check();
	}
	return;
}

void block() {
	// Create New Level
	level++;
	declarations();
	// If there is not a stoppping error run statement
	if (error != -1) {
		statement();
		// If there is not a stoppping error from statement, mark all symbols at this level to be inaccessible
		if (error != -1) {
			mark();
			level--;
		}
	}
	return;
}

void variables(int var_count) {
	char* name_ptr; // Cache identifier name for add_symbol
	token_index++;
	if (tokens[token_index].type == identifier) { // First should be an identifier
		if (multiple_declaration_check(tokens[token_index].identifier_name) != -1) { // The identifier should be valid
			print_parser_error(3,0);
			error = 1;
		}
		name_ptr = tokens[token_index].identifier_name; // The identifier name location is cached
		token_index++;
	}
	else {
		print_parser_error(2,2);
		if (tokens[token_index].type != semicolon) {
			error = -1;
			return;
		}
		error = 1;
		name_ptr = NULL;
	}
	add_symbol(2,name_ptr,0,level,var_count + 3); // The symbol is added to the table
	if (tokens[token_index].type == semicolon) { // Then there should be a semicolon
		token_index++;
	}
	else {
		print_parser_error(6,2);
		special_error_check();
	}
	return;
}
void declarations() {
	// Track Variables() calls for addressing
	int variable_calls = 0;
	while (1) {
		// No need to increment in loop as the function calls will increment
		int temp_token_type = tokens[token_index].type;
		// If Token is not a declaration INC to create space for activation record
		if (temp_token_type != keyword_const && temp_token_type != keyword_var && temp_token_type != keyword_procedure) {
			emit(INC,0,variable_calls + 3);
			return;
		}
		// If Token type is constant
		if (temp_token_type == keyword_const) {
			constants();
			if(error == -1) {
				return;
			}
		}
		// Otherwise token type is variable/procedure
		else {
			// If token type is procedure
			if (temp_token_type == keyword_procedure) {
				procedures();
				if (error == -1) {
					return;
				}
			}
			// Otherwise token type is variable
			else {
				variables(variable_calls);
				variable_calls++;
				if (error == -1) {
					return;
				}
			}
		}
	}
}

void constants() {
	// Saves identifier name for add_symbol call token is incremented
	char* temp;
	// Saves number as add_symbol call token is incremented
	int someNumber;
	// Is number negative or positive
	int isMinus = 0;
	token_index++;
	// Next token should be the constant's identifier
	if (tokens[token_index].type == identifier) {
		// If there are multiple declarations with same name
		if (multiple_declaration_check(tokens[token_index].identifier_name) != -1) {
			print_parser_error(3,0);
			error = 1;
		}
		// Set temp to identifier name
		temp = tokens[token_index].identifier_name;
		token_index++;
	}
	else {
		print_parser_error(2,1);
		if (tokens[token_index].type != assignment_symbol) {			
			error = -1;
			return;
		}
		error = 1;
		temp = NULL;
	}
	// Next token should be the assignment symbol
	if (tokens[token_index].type == assignment_symbol) {
		token_index++;
	}
	else {
		print_parser_error(4,1);
		if (tokens[token_index].type != minus && tokens[token_index].type != number) {
			error = -1;
			return;
		}
	}
	// Next symbol should be a minus and a number or just a number
	if (tokens[token_index].type == minus) {
		isMinus = 1;
		token_index++;
	}
	if (tokens[token_index].type == number) {
		someNumber = tokens[token_index].number_value;
		token_index++;
	}
	else {
		print_parser_error(5,0);
		if (tokens[token_index].type != semicolon) {
			error = -1;
			return;
		}
		error = 1;
		someNumber = 0;
	}
	// Now we have number so apply minus sign if present
	if (isMinus) {
		someNumber *= -1;
	}
	// Add to symbol table
	add_symbol(identifier,temp,someNumber, level, 0);
	// check for semicolon
	if (tokens[token_index].type == semicolon) {
		token_index++;
	}
	else {
		print_parser_error(6,1);
		special_error_check();
	}
	return;
}
// Adds instruction to code array
void emit(int op, int l, int m)
{
	code[code_index].op = op;
	code[code_index].l = l;
	code[code_index].m = m;
	code_index++;
}
// Adds symbol to symbol table
void add_symbol(int kind, char name[], int value, int level, int address)
{
	table[table_index].kind = kind;
	strcpy(table[table_index].name, name);
	table[table_index].value = value;
	table[table_index].level = level;
	table[table_index].address = address;
	table[table_index].mark = 0;
	table_index++;
}
// Marks all symbols from current procedure making them inaccessible to other procedures at higher levels 
void mark()
{
	int i;
	for (i = table_index - 1; i >= 0; i--)
	{
		if (table[i].mark == 1)
			continue;
		if (table[i].level < level)
			return;
		table[i].mark = 1;
	}
}
// Checks if the identifier name is valid for current level
int multiple_declaration_check(char name[])
{
	int i;
	for (i = 0; i < table_index; i++)
		if (table[i].mark == 0 && table[i].level == level && strcmp(name, table[i].name) == 0)
			return i;
	return -1;
}
// Searches for symbol to make sure name and kind are valid for current level
int find_symbol(char name[], int kind)
{
	int i;
	int max_idx = -1;
	int max_lvl = -1;
	for (i = 0; i < table_index; i++)
	{
		if (table[i].mark == 0 && table[i].kind == kind && strcmp(name, table[i].name) == 0)
		{
			if (max_idx == -1 || table[i].level > max_lvl)
			{
				max_idx = i;
				max_lvl = table[i].level;
			}
		}
	}
	return max_idx;
}
// Prints error depending on code and case
void print_parser_error(int error_code, int case_code)
{
	switch (error_code)
	{
		case 1 :
			printf("Parser Error 1: missing . \n");
			break;
		case 2 :
			switch (case_code)
			{
				case 1 :
					printf("Parser Error 2: missing identifier after keyword const\n");
					break;
				case 2 :
					printf("Parser Error 2: missing identifier after keyword var\n");
					break;
				case 3 :
					printf("Parser Error 2: missing identifier after keyword procedure\n");
					break;
				case 4 :
					printf("Parser Error 2: missing identifier after keyword call\n");
					break;
				case 5 :
					printf("Parser Error 2: missing identifier after keyword read\n");
					break;
				case 6 :
					printf("Parser Error 2: missing identifier after keyword def\n");
					break;
				default :
					printf("Implementation Error: unrecognized error code\n");
			}
			break;
		case 3 :
			printf("Parser Error 3: identifier is declared multiple times by a procedure\n");
			break;
		case 4 :
			switch (case_code)
			{
				case 1 :
					printf("Parser Error 4: missing := in constant declaration\n");
					break;
				case 2 :
					printf("Parser Error 4: missing := in assignment statement\n");
					break;
				default :				
					printf("Implementation Error: unrecognized error code\n");
			}
			break;
		case 5 :
			printf("Parser Error 5: missing number in constant declaration\n");
			break;
		case 6 :
			switch (case_code)
			{
				case 1 :
					printf("Parser Error 6: missing ; after constant declaration\n");
					break;
				case 2 :
					printf("Parser Error 6: missing ; after variable declaration\n");
					break;
				case 3 :
					printf("Parser Error 6: missing ; after procedure declaration\n");
					break;
				case 4 :
					printf("Parser Error 6: missing ; after statement in begin-end\n");
					break;
				default :				
					printf("Implementation Error: unrecognized error code\n");
			}
			break;
		case 7 :
			printf("Parser Error 7: procedures and constants cannot be assigned to\n");
			break;
		case 8 :
			switch (case_code)
			{
				case 1 :
					printf("Parser Error 8: undeclared identifier used in assignment statement\n");
					break;
				case 2 :
					printf("Parser Error 8: undeclared identifier used in call statement\n");
					break;
				case 3 :
					printf("Parser Error 8: undeclared identifier used in read statement\n");
					break;
				case 4 :
					printf("Parser Error 8: undeclared identifier used in define statement\n");
					break;
				case 5 :
					printf("Parser Error 8: undeclared identifier used in arithmetic expression\n");
					break;
				default :				
					printf("Implementation Error: unrecognized error code\n");
			}
			break;
		case 9 :
			printf("Parser Error 9: variables and constants cannot be called\n");
			break;
		case 10 :
			printf("Parser Error 10: begin must be followed by end\n");
			break;
		case 11 :
			printf("Parser Error 11: if must be followed by then\n");
			break;
		case 12 :
			printf("Parser Error 12: while must be followed by do\n");
			break;
		case 13 :
			printf("Parser Error 13: procedures and constants cannot be read\n");
			break;
		case 14 :
			printf("Parser Error 14: variables and constants cannot be defined\n");
			break;
		case 15 :
			printf("Parser Error 15: missing {\n");
			break;
		case 16 :
			printf("Parser Error 16: { must be followed by }\n");
			break;
		case 17 :
			printf("Parser Error 17: missing relational operator\n");
			break;
		case 18 :
			printf("Parser Error 18: procedures cannot be used in arithmetic\n");
			break;
		case 19 :
			printf("Parser Error 19: ( must be followed by )\n");
			break;
		case 20 :
			printf("Parser Error 20: invalid expression\n");
			break;
		case 21 :
			printf("Parser Error 21: procedure being called has not been defined\n");
			break;
		case 22 :
			printf("Parser Error 22: procedures can only be defined within the procedure that declares them\n");
			break;
		case 23 :
			printf("Parser Error 23: procedures cannot be defined multiple times\n");
			break;
		default:
			printf("Implementation Error: unrecognized error code\n");

	}
}
// Prints assembly code in code array
void print_assembly_code()
{
	int i;
	printf("Assembly Code:\n");
	printf("Line\tOP Code\tOP Name\tL\tM\n");
	for (i = 0; i < code_index; i++)
	{
		printf("%d\t%d\t", i, code[i].op);
		switch(code[i].op)
		{
			case LIT :
				printf("LIT\t");
				break;
			case OPR :
				switch (code[i].m)
				{
					case ADD :
						printf("ADD\t");
						break;
					case SUB :
						printf("SUB\t");
						break;
					case MUL :
						printf("MUL\t");
						break;
					case DIV :
						printf("DIV\t");
						break;
					case EQL :
						printf("EQL\t");
						break;
					case NEQ :
						printf("NEQ\t");
						break;
					case LSS :
						printf("LSS\t");
						break;
					case LEQ :
						printf("LEQ\t");
						break;
					case GTR :
						printf("GTR\t");
						break;
					case GEQ :
						printf("GEQ\t");
						break;
					default :
						printf("err\t");
						break;
				}
				break;
			case LOD :
				printf("LOD\t");
				break;
			case STO :
				printf("STO\t");
				break;
			case CAL :
				printf("CAL\t");
				break;
			case RTN :
				printf("RTN\t");
				break;
			case INC :
				printf("INC\t");
				break;
			case JMP :
				printf("JMP\t");
				break;
			case JPC :
				printf("JPC\t");
				break;
			case SYS :
				switch (code[i].m)
				{
					case WRT :
						printf("WRT\t");
						break;
					case RED :
						printf("RED\t");
						break;
					case HLT :
						printf("HLT\t");
						break;
					default :
						printf("err\t");
						break;
				}
				break;
			default :
				printf("err\t");
				break;
		}
		printf("%d\t%d\n", code[i].l, code[i].m);
	}
	printf("\n");
}
// Prints symbol table array
void print_symbol_table()
{
	int i;
	printf("Symbol Table:\n");
	printf("Kind | Name        | Value | Level | Address | Mark\n");
	printf("---------------------------------------------------\n");
	for (i = 0; i < table_index; i++)
		printf("%4d | %11s | %5d | %5d | %5d | %5d\n", table[i].kind, table[i].name, table[i].value, table[i].level, table[i].address, table[i].mark); 
	printf("\n");
}