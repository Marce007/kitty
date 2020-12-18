/* kitty: C++ truth table library
 * Copyright (C) 2017-2020  EPFL
 *
 * Permission is hereby granted, free of charge, to any person
 * obtaining a copy of this software and associated documentation
 * files (the "Software"), to deal in the Software without
 * restriction, including without limitation the rights to use,
 * copy, modify, merge, publish, distribute, sublicense, and/or sell
 * copies of the Software, and to permit persons to whom the
 * Software is furnished to do so, subject to the following
 * conditions:
 *
 * The above copyright notice and this permission notice shall be
 * included in all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
 * EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES
 * OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
 * NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT
 * HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY,
 * WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
 * FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR
 * OTHER DEALINGS IN THE SOFTWARE.
 */

/*!
  \file threshold_identification.hpp
  \brief Threshold logic function identification

  \author CS-472 2020 Fall students
*/

#pragma once

#include <lpsolve/lp_lib.h> /* uncomment this line to include lp_solve */
#include "operations.hpp"
#include "bit_operations.hpp"

enum Constraint_Type {
  GREATER,
  LESS
};
/* >=      <= */

struct Constraint {
  std::vector<uint64_t> variables;
  std::vector<int64_t> coefficients;
  Constraint_Type type;
  int constant; /* the right-hand side constant */
};


namespace kitty
{

/*! \brief Threshold logic function identification

  Given a truth table, this function determines whether it is a threshold logic function (TF)
  and finds a linear form if it is. A Boolean function is a TF if it can be expressed as

  f(x_1, ..., x_n) = \sum_{i=1}^n w_i x_i >= T

  where w_i are the weight values and T is the threshold value.
  The linear form of a TF is the vector [w_1, ..., w_n; T].

  \param tt The truth table
  \param plf Pointer to a vector that will hold a linear form of `tt` if it is a TF.
             The linear form has `tt.num_vars()` weight values and the threshold value
             in the end.
  \return `true` if `tt` is a TF; `false` if `tt` is a non-TF.
*/
template<typename TT, typename = std::enable_if_t<is_complete_truth_table<TT>::value>>
bool is_threshold( TT& tt, std::vector<int64_t>* plf = nullptr )
{
  std::vector<int64_t> linear_form;

  uint64_t numvars = tt.num_vars();
  uint64_t numbits = tt.num_bits();
  uint64_t  count_neg;
  uint64_t  count_pos;
  bool is_negative;
  bool is_positive;

  //Check for unateness
  for ( auto i = 0u; i < numvars; i++ )
  {
    is_negative = false;
    is_positive = false;
    count_neg=0;
    count_pos=0;
    auto const negative_cof = cofactor0( tt, i );
    auto const positive_cof = cofactor1( tt, i );
    for ( auto bit = 0; bit < ( 2 << ( numvars - 1 ) ); bit++ )
    {
      if ( get_bit( positive_cof, bit ) <= get_bit( negative_cof, bit ) )
        count_neg++;
      if ( get_bit( positive_cof, bit ) >= get_bit( negative_cof, bit ) )
        count_pos++;
    }
    if (count_neg == numbits )  //If all f(xi) <= f(xi'): negative unate
      is_negative = true;
    if (count_pos == numbits )  //If all f(xi) => f(xi'): positive unate
      is_positive = true;
    if (is_negative)  //If negative, I make it positive
      flip_inplace(tt, i);
    if (!is_negative && !is_positive) //If the function is binate
      return false;
  }

  //Constraints for ILP
  std::vector<Constraint> constraints;
  //I set => or <= and the constant considering each bit of the tt
  for(uint64_t bit=0; bit < numbits; bit++){
    Constraint constraint;
    auto bit_value = get_bit(tt, bit);
      if(bit_value == 0){
        constraint.type = LESS;
        constraint.constant = -1;
      }
      else if( bit_value == 1){
        constraint.type = GREATER;
        constraint.constant = 0;
      }
    for(uint64_t var = 0; var <= numvars; var++){
      constraint.variables.emplace_back(var);
    }
    constraints.emplace_back(constraint);
  }

  //I create the coefficient of for each equation
  for(uint64_t var = 0; var < numvars; var++){
    uint8_t binary_coeff = 0;
    uint64_t recurrency = 1u << var;
    uint64_t recurrency_tmp = 1u << var;
    for (uint64_t bit = 0; bit < numbits; bit++)
    {
      if ( bit < recurrency )
        constraints[bit].coefficients.emplace_back( binary_coeff );
      else
      {
        recurrency = recurrency + recurrency_tmp;
        binary_coeff = !binary_coeff;
        constraints[bit].coefficients.emplace_back( binary_coeff );
      }
    }
  }

  //T has always -1 as coefficient
  for(uint64_t bit = 0; bit < numbits; bit++){
    constraints[bit].coefficients.emplace_back(-1);
  }

  //I set each weight to be positive
  for(uint64_t var = 0; var <= numvars; var++){
    Constraint constraint;
    for(uint64_t i = 0; i <= numvars; i++){
      constraint.coefficients.emplace_back(0);
    }
    constraint.type = GREATER;
    constraint.constant = 0;
    constraint.coefficients[var] = 1;
    constraint.variables.emplace_back(var);
    constraints.emplace_back(constraint);
  }

  //lp_solve
  lprec *lp;
  auto num_rows = constraints.size();
  std::vector<double> row;

  /* Create a new LP model */
  lp = make_lp(0, numvars +1);
  if(lp == nullptr) {
    fprintf(stderr, "Unable to create new LP model\n");
    return(false);
  }

  set_add_rowmode(lp, TRUE);

  /*the objective function*/
  row.emplace_back(1.0);
  for(uint64_t col = 1; col<= numvars +1; col++){
    row.emplace_back(1.0);
  }

  set_obj_fn(lp, row.data());

  for(uint64_t rows = 0; rows < num_rows; rows++){
    for(uint64_t col = 1; col <= numvars +1; col++){
      row[col] = constraints[rows].coefficients[col-1];
    }
    if(constraints[rows].type == GREATER )
      add_constraint(lp, row.data(), GE, constraints[rows].constant);
    else if (constraints[rows].type == LESS )
      add_constraint(lp, row.data(), LE, constraints[rows].constant);
  }

  set_add_rowmode(lp, FALSE);
  set_minim(lp);
  print_lp(lp);
  set_verbose(lp, IMPORTANT);

  for(auto i = 1u; i< numvars +1; i++){
    set_int(lp, i, TRUE);
  }

  int ret = solve(lp);
  if(ret == OPTIMAL){    //tt is TF
    /* variable values */
    get_variables(lp, row.data());
    for(uint64_t i = 0; i < numvars +1; i++){
      /* push the weight and threshold values into `linear_form` */
      linear_form.push_back((int)(row[i]));
    }
  }
  else
    return false;


  if ( plf ){
    *plf = linear_form;
  }
  return true;
}


} /* namespace kitty */
