#include <iostream>
#include <vector>
#include <utility>
#include <set>
#include <cmath>
#include <algorithm>
#include <chrono>
#include <fstream>
#include <string>
#include <boost/dynamic_bitset.hpp>

using namespace std;
using res_type = set <pair <boost::dynamic_bitset<>, boost::dynamic_bitset<> > >;

// оператор вывода для строк (в случае столбцов передается транспонированная матрица)
//
// matrix - булева матрица
//
// set - битсет, размерность которого совпадает с количеством строк в матрице
// в нем бит равен 1, если строка входит в множество
boost::dynamic_bitset<> derOp (vector <boost::dynamic_bitset<> > &matrix,
                               boost::dynamic_bitset<> &set)
{
    short num_attr = matrix[0].size();
    
    boost::dynamic_bitset<> res (num_attr);
    res.set();
    
    short idx = set.find_first();
    
    while (idx != -1)
    {
        res &= matrix[idx];
        idx = set.find_next(idx);
    }
    
    return res;
}

// разница множеств (через битсеты)
boost::dynamic_bitset<> bitset_diff (const boost::dynamic_bitset<> &bitset1,
                                     const boost::dynamic_bitset<> &bitset2)
{
    boost::dynamic_bitset<> res (bitset1.size());
    res.set();
    
    res ^= bitset2;
    res &= bitset1;
    
    return res;
}

// рекурсивная функция process
void process (boost::dynamic_bitset<> &A,
              short &g,
              boost::dynamic_bitset<> &C, // C = A''
              boost::dynamic_bitset<> &D, // D = A'
              vector <boost::dynamic_bitset<> > &matrix,
              vector <boost::dynamic_bitset<> > &matrix_t, // транспонированная matrix
              res_type &concept_set)
{
    auto diff = bitset_diff(C, A);
    
    auto idx = diff.find_first();
    
    if ((idx != -1) && (idx < g)) // множество непусто
        return;
    
    concept_set.insert(make_pair(C, D));
    
    short num_obj = matrix.size();
    
    for (short i=g+1; i<num_obj; i++)
    {
        C.set(i); // это и есть Z
        
        boost::dynamic_bitset<> Y = D;
        Y &= matrix[i];

        auto X = derOp(matrix_t, Y);
        
        if (concept_set.size() < 5000000) // здесь было использовано ограничение для тех задач, где
                                          // было слишком большое количество генерируемых формальных понятий
            process(C, i, X, Y, matrix, matrix_t, concept_set);
        
        C.reset(i);
    }
}

// алгоритм close by one
res_type cbo (vector <boost::dynamic_bitset<> > &matrix,
              vector <boost::dynamic_bitset<> > &matrix_t) // транспонированная matrix
{
    res_type concept_set;
    short num_obj = matrix.size();
    short num_atr = matrix[0].size();
    
    boost::dynamic_bitset<> tmp (num_obj);
    
    for (short i=0; i<num_obj; i++)
    {
        tmp.set(i);
        
        auto D = derOp(matrix, tmp);
        auto C = derOp(matrix_t, D);
        
        if (concept_set.size() < 5000000) // здесь было использовано ограничение для тех задач, где
                                          // было слишком большое количество генерируемых формальных понятий
            process(tmp, i, C, D, matrix, matrix_t, concept_set);
        
        tmp.reset(i);
    }
    
    auto A = derOp(matrix, tmp);
    auto B = derOp(matrix_t, A);
    
    concept_set.insert(make_pair(B, A));
    
    return concept_set;
}

// транспонирование матрицы
vector <boost::dynamic_bitset<> > transpose(vector <boost::dynamic_bitset<> > &matrix)
{
    vector <boost::dynamic_bitset<> > result(matrix[0].size(), boost::dynamic_bitset<> (matrix.size()));
    
    for (int i=0; i<matrix[0].size(); i++)
        for (int j=0; j<matrix.size(); j++)
            result[i][j] = matrix[j][i];
    
    return result;
}

// функция B с волной
//
// obj - объект (признаковое описание)
//
// B - признаки элементарного классификатор (все)
bool contains (const boost::dynamic_bitset<> &obj, const boost::dynamic_bitset<> &B)
{
    boost::dynamic_bitset<> tmp1 = obj;
    boost::dynamic_bitset<> tmp2 = ~B;
    
    tmp1 |= tmp2;
    
    if (tmp1.count() != tmp1.size())
        return false;
    else
        return true;
}

// функция для генерации гипотез
// если positive == true, то генерирует гипотезы класса К, иначе !К
// если optim == true, то транспонируем матрицу
set <boost::dynamic_bitset<>> hypothesesMaker(vector <boost::dynamic_bitset<> > &matrix,
                                               vector <int> &target,
                                               bool positive,
                                               bool optim)
{
    vector <boost::dynamic_bitset<> > X;
    vector <boost::dynamic_bitset<> > Y;
    
    // выделим нужные подматрицы с нужным таргетом
    // X - для нахождения понятий
    // Y - для перебора противоположных объектов

    if (positive)
        for (int i=0; i<target.size(); i++)
        {
            if (target[i] == 1)
                X.push_back(matrix[i]);
            else
                Y.push_back(matrix[i]);
        }
    else
        for (int i=0; i<target.size(); i++)
        {
            if (target[i] == 0)
                X.push_back(matrix[i]);
            else
                Y.push_back(matrix[i]);
        }

    // для начала найдём все формальные понятия положительного/отрицательного контекста
    // затем выберем из них те, которые удовлеторяют определению гипотезы
    auto X_t = transpose(X);
    
    res_type concepts;
    
    if (not optim)
    {
        concepts = cbo(X, X_t);
    }
    else
    {
        res_type new_concepts;

        new_concepts = cbo(X_t, X);
        
        for (auto it=new_concepts.begin(); it!=new_concepts.end(); it++)
            concepts.insert(make_pair((*it).second, (*it).first));
    }
    
    set <boost::dynamic_bitset<>> hypotheses;
    bool is_hypothese, is_contained;
    
    for (auto it=concepts.begin(); it!=concepts.end(); it++)
    {
        is_hypothese = true;
        
        for (int m=0; m!=Y.size(); m++)
        {
            is_contained = contains(Y[m], (*it).second);
            
            if (!is_contained)
                continue;
            else
            {
                is_hypothese = false;
                break;
            }
        }

        if (is_hypothese)
            hypotheses.insert((*it).second);
    }
    
    return hypotheses;
}

// дсм-метод, возвращающий y_proba (y_proba_golos), время fit'a и количество гипотез для положительного/отрицательного классов
// если optim == true, то транспонируем матрицу
tuple < vector <float>, vector <float>, long long int, int, int> jsm (vector <boost::dynamic_bitset<> > &X_train,
                                                                      vector <boost::dynamic_bitset<> > &X_test,
                                                                      vector <boost::dynamic_bitset<> > &X_train_inv, // X_train с обратным порядком
                                                                      vector <boost::dynamic_bitset<> > &X_test_inv, // X_test с обратным порядком
                                                                      vector <int> &y_train,
                                                                      bool optim)
{
    chrono::steady_clock::time_point begin = chrono::steady_clock::now();

    auto pos_hyp = hypothesesMaker(X_train, y_train, true, optim);
    
    auto neg_hyp = hypothesesMaker(X_train_inv, y_train, false, optim);
    
    chrono::steady_clock::time_point end = chrono::steady_clock::now();
    long long int time = chrono::duration_cast<chrono::microseconds>(end - begin).count();
    
    vector <float> y_proba (X_test.size(), 0);
    vector <float> y_proba_golos (X_test.size(), 0);
    
    // строгая процедура классификации
    
    bool flag_pos;
    bool flag_neg;

    for (int i=0; i!=X_test.size(); i++)
    {
        flag_pos = false;
        flag_neg = false;
        
        for (auto it=pos_hyp.begin(); it!=pos_hyp.end(); it++)
            if (contains(X_test[i], *it))
            {
                flag_pos = true;
                break;
            }
        
        for (auto it=neg_hyp.begin(); it!=neg_hyp.end(); it++)
            if (contains(X_test_inv[i], *it))
            {
                flag_neg = true;
                break;
            }

        if (flag_neg and flag_pos)
            y_proba[i] = 0; // противоречивая классификация
        else if (flag_pos)
            y_proba[i] = 1; // положительный класс
        else if (flag_neg)
            y_proba[i] = 0; // отрицательный класс
        else
            y_proba[i] = 0.5; // неопределенная классификация
    }
    
    // голосование

    float count_pos;
    float count_neg;

    for (int i=0; i!=X_test.size(); i++)
    {
        count_pos = 0;
        count_neg = 0;
        
        for (auto it=pos_hyp.begin(); it!=pos_hyp.end(); it++)
            if (contains(X_test[i], *it))
                count_pos++;
        
        for (auto it=neg_hyp.begin(); it!=neg_hyp.end(); it++)
            if (contains(X_test_inv[i], *it))
                count_neg++;
    
        if (count_pos == count_neg)
        {
            y_proba_golos[i] = 0.5; // противоречивая классификация
        } else {
            y_proba_golos[i] = count_pos/(count_pos + count_neg); // положительный класс
        }
    }

    int pos_size = pos_hyp.size();
    int neg_size = neg_hyp.size();
    
    return make_tuple(y_proba, y_proba_golos, time, pos_size, neg_size);
}

int main(int argc, const char * argv[])
{
    for (int i=0; i<10; i++)
    {
        vector <boost::dynamic_bitset<> > X_train;
        vector <boost::dynamic_bitset<> > X_test;
        vector <boost::dynamic_bitset<> > X_train_inv; // X_train с обратным порядком
        vector <boost::dynamic_bitset<> > X_test_inv; // X_test с обратным порядком
 
        vector <int> y_train;
        vector <int> y_test;

        string s;
        boost::dynamic_bitset<> row;

        fstream train;
        
        // сюда подаем обучающую выборку с обычным порядком
        train.open("datasets_chum/sarkoma_chum/sarkoma_chum_new_m" + to_string(i), ios::in);

        while (1)
        {
            train >> s;
            if (train.eof())
                break;

            // здесь вместо "101" и "102" пишем лейблы классов
            // причем лейблы должны отличаться от 0 и 1 !!!
            if (not (s == "0" || s == "1" || s == "101" || s== "102"))
                continue;

            // аналогично
            if (s == "101" || s == "102")
            {
                // здесь лейбл положительного класса
                y_train.push_back(s == "101" ? 1 : 0);
                X_train.push_back(row);
                row.clear();
            }
            else
                row.push_back(stoi(s));
        }
        
        train.close();
        
        // сюда подаем обучающую выборку с обратным порядком
        train.open("datasets_chum/sarkoma_chum/sarkoma_chum_new_m_inv" + to_string(i), ios::in);

        while (1)
        {
            train >> s;
            if (train.eof())
                break;
            
            // здесь вместо "101" и "102" пишем лейблы классов
            // причем лейблы должны отличаться от 0 и 1 !!!
            if (not (s == "0" || s == "1" || s == "101" || s== "102"))
                continue;

            // аналогично
            if (s == "101" || s == "102")
            {
                X_train_inv.push_back(row);
                row.clear();
            }
            else
                row.push_back(stoi(s));
        }

        fstream test;
        
        // сюда подаем тестовую выборку с обычным порядком
        test.open("datasets_chum/sarkoma_chum/sarkoma_chum_test_new_m" + to_string(i), ios::in);

        while (1)
        {
            test >> s;
            if (test.eof())
                break;

            // здесь вместо "101" и "102" пишем лейблы классов
            // причем лейблы должны отличаться от 0 и 1 !!!
            if (not (s == "0" || s == "1" || s == "101" || s == "102"))
                continue;
            
            // аналогично
            if (s == "101" || s == "102")
            {
                // здесь лейбл положительного класса
                y_test.push_back(s == "101" ? 1 : 0);
                X_test.push_back(row);
                row.clear();
            }
            else
                row.push_back(stoi(s));
        }
        
        test.close();
        
        // сюда подаем тестовую выборку с обратным порядком
        test.open("datasets_chum/sarkoma_chum/sarkoma_chum_test_new_m_inv" + to_string(i), ios::in);

        while (1)
        {
            test >> s;
            if (test.eof())
                break;
            
            // здесь вместо "101" и "102" пишем лейблы классов
            // причем лейблы должны отличаться от 0 и 1 !!!
            if (not (s == "0" || s == "1" || s == "101" || s == "102"))
                continue;
            
            // аналогично
            if (s == "101" || s == "102")
            {
                X_test_inv.push_back(row);
                row.clear();
            }
            else
                row.push_back(stoi(s));
        }

        vector <float> y_proba;
        vector <float> y_proba_golos;
        long long int time;
        int pos_size;
        int neg_size;

        tie(y_proba, y_proba_golos, time, pos_size, neg_size) = jsm(X_train, X_test,
                                                                    X_train_inv, X_test_inv,
                                                                    y_train, false);

        fstream res;
        
        // директория для результата
        res.open("datasets_chum/sarkoma_chum_res/res" + to_string(i), ios::out);

        for (auto it=y_test.begin(); it!=y_test.end(); it++)
            res << *it << " ";
        res << endl;

        for (auto it=y_proba.begin(); it!=y_proba.end(); it++)
            res << *it << " ";
        res << endl;

        for (auto it=y_proba_golos.begin(); it!=y_proba_golos.end(); it++)
            res << *it << " ";
        res << endl;
        
        res << pos_size << endl;
        res << neg_size << endl;
        res << time << endl;
        
        res.close();
        
        // в итоге в файле получается шесть строк:
        // 1 - y_test
        // 2 - y_proba для строгой процедуры классификации
        // 3 - y_proba для голосования
        // 4 - количество гипотез положительного класса
        // 5 - количество гипотез отрицательного класса
        // 6 - время обучения
    }
}
