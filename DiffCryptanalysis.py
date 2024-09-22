#ECE 506 Project Code for Differential Cryptanalysis Attack
#Written by Payton Murdoch, V00904677
#Tasks Accomplished:
#   The approach we took for this code is to be able to apply this differential cryptanalysis attack on generalized toy ciphers with the same rounds whos S-box and permutations vary.
#   This code, explores the possible differential characteristic which yields the highest probability for each of the partial keys noting all the keys influenced by the differential.
#   With this in mind, it is important to note that we went beyond the scope of the original task requirements allowing our code to compute the entire last round key and not just 8 bits.
#This code carries with it a few assumptions:
#   First, we note that the key bits are generated at random with a 50% probability of being 0 or 1 as noted in the Key_Schedule function and assumed in the tutorial.
#   With regard to the input key, round keys are independent to the input/master key in computation, however, they are related as the input/master key is used as the random seed for consistency purposes.
#   Secondly, while computing differential characteristics, in this case Partial key K5-K8 and K13-K16 have the same characteristic/are related so it may seem redundant to calculate this twice as independent sets.
#   However, this may not be the case for all s-box and permutation network combinations thus each partial key is considered as an independent set
#   and we note/calculate the all keys influenced by the differential to determine/verify the best fit result. 
#   Lastly, when determining Differential characteristics for each s-box, if there exists multiple identical probabilities that are the highest chance, then the code selects the first option.
#   This was a restriction implemented so that the code in that section can remain relatively straight forward and not take up too much computation time.
import sys
import random
import math
import threading
import collections

#S_box Constant takes 4-bits as input. S_box[input] = output
S_box = [14,4,13,1,2,15,11,8,3,10,6,12,5,9,0,7]

#P_pos takes bit position as input. P_pos[input bit pos] = output bit pos
P_pos = [0,4,8,12,1,5,9,13,2,6,10,14,3,7,11,15]

#Key_schedule, in accordance with the implementation document, bits of the round keys are generated independently and randomly.
#As such for each of the 5 round keys generated their only relation to the master key is that it is used to seed the random.randint probabilities.
#random.randint should exhibit an approximate 50% probability of selecting 1 or 0 for each key bit thus random and independent bits.
#Output is the 5 round keys.
def Key_Schedule(key):
    Output =[]
    for x in range(0,5):
        key_bits =[0]*16 
        for x in range(0,16):
            key_bits[x]= (random.randint(0,1))
        total = 0
        for x in range(0,16):
            total = total + key_bits[15-x]*pow(2, x)
        Output.append(total)
    return Output

#Get_Bit_Array, takes an input of a denoted size and outputs the corresponding array of bits in proper order.
def Get_Bit_Array(input, size):
    new_input = input
    bit_array = [0]*size
    for i in range(0, size):
        output = new_input %2
        bit_array[size-1-i] = output
        new_input = math.floor(new_input/2)
    return bit_array        

#Substitution works on the 4 bit groupings of each region of a 16 bit array. Changing values in accordance with the S_Box.
def Substitution(bit_array):
    Result_arr = [0]*16
    count = 0
    total_sum = 0
    while count <16:
        for x in range(0,4):
            total_sum = total_sum + (bit_array[count+x]*pow(2,3-x))
        result = S_box[total_sum]
        temp_array = Get_Bit_Array(result, 4)
        for x in range(0,4):
            Result_arr[count+x] = temp_array[x]
        count = count + 4
        total_sum = 0
    return Result_arr

#As described with P_pos, permutation works on the array of bits as a whole and returns the bits in permuted positions.
def Permutation(bit_array):
    Result_arr = [0]*16
    for x in range(0,16):
        Result_arr[P_pos[x]] = bit_array[x]
    return Result_arr

#Where the toy cipher computation begins, taking the value and round keys as input. 
#The value will go through 4 rounds in the SPN where it will be masked with the round keys, split and thrown into S-boxes and then permuted.
#Resulting value will be masked by the last round key can be our resulting ciphertext represented as an integer value.
def Rounds(value, keys):
    new_value = value
    for x in range(0,4):
        mask = new_value ^ keys[x]
        bit_arr = Get_Bit_Array(mask, 16)
        new_arr = Substitution(bit_arr)
        if x < 3:
            permute_arr = Permutation(new_arr)
        else:
            permute_arr = new_arr
        total = 0
        for x in range(0,16):
            total = total + permute_arr[15-x]*pow(2, x)
        new_value = total
    return (new_value ^ keys[4])

#As our threaded processes output to the same list, a sorting key on probabilities for differentials can help with organization.
def sorter1(tuple):
    return tuple['probability']

#Having a sorted function for
def sorter2(dict):
    return dict['freq']

#Creates a matrix for differential distributions based on the S-boxes.
def Differentials():
    differential_table = [[0 for _ in range(16)] for _ in range(16)]
    for x1 in range(0,16):
        for x2 in range(0,16):
            differential_table[x1^x2][S_box[x1]^S_box[x2]] = differential_table[x1^x2][S_box[x1]^S_box[x2]] +1
    return differential_table

#Similar to the Subsitution function, this one instead utilizes the differential distribution tables.
#This determines the output based on the differential outputs with the highest probabilities.
#Returns, the resulting differential bit array and the resulting probability at the time step represented as
#numerator (num) and denominator (denom).
def diff_Substitution(bit_array, table):
    num = 1
    denom = 1
    Result_arr = [0]*16
    count = 0
    total_sum = 0
    while count <16:
        for x in range(0,4):
            total_sum = total_sum + (bit_array[count+x]*pow(2,3-x))
        freq = 0
        result = 0
        for y in table:
            if total_sum == y['Dx']:
                if y['freq'] > freq:
                    result = y['Dy']
                    freq = y['freq']
        if freq != 0:
            denom = denom*16
            num = num*freq
        temp_array = Get_Bit_Array(result, 4)
        for x in range(0,4):
            Result_arr[count+x] = temp_array[x]
        count = count + 4
        total_sum = 0
        total = 0
    return (Result_arr, num, denom)

#Diff_rounds attributes to the R-1 round of differential calculations which result in the the denoted U4 in the tutorial document.
#This is so we can properly determine the which keys the differentials contribute to in the last round of computations.
#This function takes the differential distribution table as input and outputs the partial keys found and the probabilities.
#Note: Given that this is for differentials and not the plaintext/ciphertext pairs, it does not need to utilize the keys.
def Diff_rounds(table, value):
    new_value = value
    num = 1
    denom = 1
    bit_arr = Get_Bit_Array(new_value, 16)
    for x in range(0,3):
        new_arr,new_num, new_denom = diff_Substitution(bit_arr, table)
        num = num * new_num
        denom = new_denom *denom
        permute_arr = Permutation(new_arr)
        bit_arr = permute_arr
    count = 0
    partial_keys = [0]*4
    while count < 4:
        for x in range(0,4):
            if bit_arr[x+(count*4)] == 1:
                partial_keys[count] = 1
        count = count +1
    total = 0
    for x in range(16):
        total = total + bit_arr[x]*pow(2,15-x)
    return(partial_keys, num/denom, total)

#As we want to compute over the total range of input differentials we will run as a threaded process to parallelize computation.
#taking the range of values, dictionary and differential table as the input it simply stores results in the dictionary.
def threaded_dif_init(range_start,range_end, dictionary,table):
    for x in range(range_start, range_end):
        keys, fract, total = Diff_rounds(table, x)
        dictionary.append({'input differential':x, 'Binary':'{0:016b}'.format(x), 'U4':total, 'U4 Binary':'{0:016b}'.format(total),'partial keys':keys, 'probability': fract})
    return

#part_keys, the most verbose function in the code is an effort to automate the entire process to determine the partial keys.
#This function takes the list of input pairs whose differentials match in accordance with one of the printed characteristics, the characteristics and the round keys.
#First, this function computes the completed Ciphertext of each of the differentials then computes them as their corresponding bit arrays.
#Secondly the function then iterates through the bit arrays capturing 4 bits at a time and partially decrypting the cipher.
#The aforementioned partial decryption attempts to XOR the input pairs with each of the values between 0-15 (reversing round key).
#The unkeyed 4-bit segments are then put through the s-box in reverse so that we get the U4 value for the input pairs.
#If the U4 differential matches the computed U4 passed with the differential characteristic then it is stored as a possible key value.
#Once all possible key values are found for a pair based on the partial keys it attributes to, then the code appends each combination of possible keys to a list.
#After running through all pairs the code returns a list using the collections.Counter function which returns a list of {partial key, frequency} pairs.
#This will then be used to determine which partial key occurs the most resulting the values for the last round key.
def part_keys(pair_list, differential, keys):
    probabilities = []
    for x in pair_list:
        new_list = list(x)
        partial_key = differential['partial keys']
        cipher1 = Rounds(new_list[0], keys)
        cipher2 = Rounds(new_list[1], keys)
        count = 0
        cipher_b1 = Get_Bit_Array(cipher1, 16)
        cipher_b2 = Get_Bit_Array(cipher2, 16)
        U4_bits = Get_Bit_Array(differential['U4'],16)
        sub_sets = []
        records = 0
        index = 0
        while count < 4:
            if partial_key[count] == 1:
                sub_sets.append([])
                records = records+1
                total_b1 = 0
                total_b2 = 0
                total_U4 = 0
                for y in range(4):
                    total_b1 = total_b1+(cipher_b1[y+(count*4)]*pow(2,3-y))
                    total_b2 = total_b2+(cipher_b2[y+(count*4)]*pow(2,3-y))
                    total_U4 = total_U4+(U4_bits[y+(count*4)]*pow(2,3-y))
                for i in range(16):
                    un_keyed1 = total_b1 ^ i
                    un_keyed2 = total_b2 ^ i
                    input_U41 = 0
                    input_U42 = 0
                    for j in range(16):
                        if un_keyed1 == S_box[j]:
                            input_U41 = j
                            break
                    for j in range(16):
                        if un_keyed2 == S_box[j]:
                            input_U42 = j
                            break
                    if (input_U41^input_U42) == total_U4:
                        sub_sets[index].append(i)
                index = index+1
            count = count +1
        if len(sub_sets) == records:
            index_counter = 1
            string = ''
            for x in sub_sets[0]:
                string = str(x)
                if len(sub_sets) == 4:
                    for y in sub_sets[1]:
                        new_string = ','+str(y)+','
                        for k in sub_sets[2]:
                            newest_string = str(k)+','
                            for j in sub_sets[3]:
                                probabilities.append(string+new_string+newest_string+str(j))
                if len(sub_sets) == 3:
                    for y in sub_sets[1]:
                        new_string = ','+str(y)+','
                        for k in sub_sets[2]:
                            probabilities.append(string+new_string+str(k))
                elif len(sub_sets) == 2:
                    for y in sub_sets[index_counter]:
                        probabilities.append(string+','+str(y))
                else:
                    probabilities.append(string)
    final_list = collections.Counter(probabilities)
    output = final_list.most_common(1)
    return(output)
    

def main():
    if len(sys.argv) != 2:
        print("ERROR, Correct Input: Python3 DiffCryptanalysis.py *key value as int 0-65535*")
        exit()
    key_value = int(sys.argv[1])
    if key_value > 65535:
        print("ERROR, Key value out of range, choose between 0-65535")
        exit()
    print("---------------------------------------")
    print("DETERMINING DIFFERENTIAL CHRACTERISTICS")
    print("---------------------------------------")
    random.seed(sys.argv[1]) #Mapping seed to the master key value so that there is relative probability consistency amongst the pseudorandom values.
    keys = Key_Schedule(key_value)
    Diff_table = Differentials()
    output = []
    #Isolate the Differential distributions to only include valid entries thus non-zero.
    for x in range(16):
        for y in range(16):
            if Diff_table[x][y] > 0  and Diff_table[x][y] < 16:
                output.append({'Dx':x, 'Dy':y,'freq':Diff_table[x][y]})
    output.sort(key=sorter2)
    new_list = []
    #Starting Multithreading processes to hasten the computation of all differentials.
    #Threads will occupy the same list which will be sorted later.
    thread1 = threading.Thread(target=threaded_dif_init, args= (1,16384,new_list,output,))
    thread2 = threading.Thread(target=threaded_dif_init, args= (16384,32768,new_list,output,))
    thread3 = threading.Thread(target=threaded_dif_init, args= (32768,49152,new_list,output,))
    thread4 = threading.Thread(target=threaded_dif_init, args= (49152,65536,new_list,output,))
    thread1.start()
    thread2.start()
    thread3.start()
    thread4.start()
    thread1.join()
    thread2.join()
    thread3.join()
    thread4.join()
    #Sorting list in reverse order based on probabilities so that all highest probabilities are in the beginning.
    new_list.sort(key=sorter1, reverse = True)
    top_entry_key1 = []
    top_entry_key2 = []
    top_entry_key3 = []
    top_entry_key4 = []
    #Parse the first values of the differential list (those with the highest probability) and in turn find the highest probability entry
    #For each partial key region K1-K4, K5-K8, K9-K12, K13-16.
    #Shows the differential characteristic based on input differential, U4 differential, partial keys attributed to entry and probability.
    for x in new_list:
        if x['partial keys'][0] == 1 and len(top_entry_key1) == 0:
            top_entry_key1 = x
        if x['partial keys'][1] == 1 and len(top_entry_key2) == 0:
            top_entry_key2 = x
        if x['partial keys'][2] == 1 and len(top_entry_key3) == 0:
            top_entry_key3 = x
        if x['partial keys'][3] == 1 and len(top_entry_key4) == 0:
            top_entry_key4 = x
        if len(top_entry_key1) != 0:
            break
    new_list.clear()
    print("Highest probability Differential for K1..K4")
    for x in top_entry_key1:
        print(x,':',top_entry_key1[x])
    print("-------------------------------------------")
    print("Highest probability Differential for K5..K8")
    for x in top_entry_key2:
        print(x,':',top_entry_key2[x])
    print("--------------------------------------------")
    print("Highest probability Differential for K9..K12")
    for x in top_entry_key3:
        print(x,':',top_entry_key3[x])
    print("---------------------------------------------")
    print("Highest probability Differential for K13..K16")
    for x in top_entry_key4:
        print(x,':',top_entry_key4[x])
    print("---------------------------------------------")
    print("DETERMINING LAST ROUND KEY FROM DIFFERENTIALS")
    print("---------------------------------------------")
    listed_values = []
    diff_k1 = []
    diff_k2 = []
    diff_k3 = []
    diff_k4 = []
    #Input differential pair computation, sample size denoted in the range() function, select a value randomly and uniquely so we do not have repetition pairs.
    #then XOR the value with the input differential characteristic, leading to a resulting second value that matches the differential requirements.
    #Do this for all differential characteristics noted in the printed statements.
    for x in range(10000):
        value = random.randint(0,65535)
        while value in listed_values:
            value = random.randint(0,65535)
        listed_values.append(value)
        diff_k1.append({value,value^top_entry_key1['input differential']})
        diff_k2.append({value,value^top_entry_key2['input differential']})
        diff_k3.append({value,value^top_entry_key3['input differential']})
        diff_k4.append({value,value^top_entry_key4['input differential']})
    #Functions to get the resulting partial key lists.
    result_1 = part_keys(diff_k1, top_entry_key1,keys)
    result_2= part_keys(diff_k2, top_entry_key2,keys)
    result_3= part_keys(diff_k3, top_entry_key3,keys)
    result_4 = part_keys(diff_k4, top_entry_key4,keys)
    print("Highest probability Partial key for K1..K4")
    print("Partial keys : ",top_entry_key1['partial keys'])
    print("Key : ",result_1[0][0])
    print("Probability : ",result_1[0][1]/10000)
    print("------------------------------------------")
    print("Highest probability Partial key for K5..K8")
    print("Partial keys : ",top_entry_key2['partial keys'])
    print("Key : ",result_2[0][0])
    print("Probability : ",result_2[0][1]/10000)
    print("-------------------------------------------")
    print("Highest probability Partial key for K9..K12")
    print("Partial keys : ",top_entry_key3['partial keys'])
    print("Key : ",result_3[0][0])
    print("Probability : ",result_3[0][1]/10000)
    print("--------------------------------------------")
    print("Highest probability Partial key for K13..K16")
    print("Partial keys : ",top_entry_key4['partial keys'])
    print("Key : ",result_4[0][0])
    print("Probability : ",result_4[0][1]/10000)
    print("------------------------------------------------")
    print("VERIFICATION: TRUE LAST ROUND KEY USED IN CIPHER")
    print("------------------------------------------------")
    key_bits = Get_Bit_Array(keys[4],16)
    count = 0
    total_sum = 0
    while count <4:
        for x in range(0,4):
            total_sum = total_sum + (key_bits[(count*4)+x]*pow(2,3-x))
        print("Key ",count+1,": ",total_sum)
        total_sum = 0
        count = count + 1
    print("------------------------------------------------")



    
    
        

if __name__ == "__main__":
    main()