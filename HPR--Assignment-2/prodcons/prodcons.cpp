/***************************************************************************
 *   Copyright (C) 2012-2013 Jan Fostier (jan.fostier@intec.ugent.be)      *
 *                                                                         *
 *   This program is free software; you can redistribute it and/or modify  *
 *   it under the terms of the GNU General Public License as published by  *
 *   the Free Software Foundation; either version 2 of the License, or     *
 *   (at your option) any later version.                                   *
 *                                                                         *
 *   This program is distributed in the hope that it will be useful,       *
 *   but WITHOUT ANY WARRANTY; without even the implied warranty of        *
 *   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the         *
 *   GNU General Public License for more details.                          *
 *                                                                         *
 *   You should have received a copy of the GNU General Public License     *
 *   along with this program; if not, write to the                         *
 *   Free Software Foundation, Inc.,                                       *
 *   59 Temple Place - Suite 330, Boston, MA  02111-1307, USA.             *
 ***************************************************************************/

#include <cstdlib>
#include <iostream>
#include <ctime>
#include <cstring>
#include <cmath>
#include <pthread.h>
#include <vector>

using namespace std;
vector<int> stack;

pthread_mutex_t mutex;
pthread_cond_t cont_var;

// ==========================================================================
// THREAD ROUTINES
// ==========================================================================

int bake()
{
  cout << "Baked donut...\n";
  return 0;
}

void* producer(void *vargs)
{
  while (true) {
    int element = bake();

    pthread_mutex_lock(&mutex);
    while (stack.size() == 10)
      pthread_cond_wait(&cont_var, &mutex);

    stack.push_back(element); // push "created" element onto the stack

    pthread_cond_signal(&cont_var);
    pthread_mutex_unlock(&mutex);
  }

  return NULL;
}

void eat(int donut)
{
  cout << "Ate donut...\n";
}

void* consumer(void *vargs)
{
  while (true) {

    pthread_mutex_lock(&mutex);
    while(stack.empty())
      pthread_cond_wait(&cont_var, &mutex);

    int donut = stack.back(); // get element
    stack.pop_back(); // remove element

    pthread_cond_signal(&cont_var);
    pthread_mutex_unlock(&mutex);

    eat(donut);
  }

  return NULL;
}

int main(int argc, char* argv[])
{
  cout << "Warning: this code runs forever..." << endl;

  pthread_t prod, cons;

  pthread_mutex_init(&mutex, NULL);
  pthread_cond_init(&cont_var, NULL);

  // create threads
  pthread_create(&prod, NULL, producer, NULL);
  pthread_create(&cons, NULL, consumer, NULL);

  // this point will never be reached ...
  pthread_join(prod, NULL);
  pthread_join(cons, NULL);

  exit(EXIT_SUCCESS);
}
