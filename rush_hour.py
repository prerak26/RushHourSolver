
from z3 import * # load z3 library
import sys

#####your python script#####

lines=[]
f = open(sys.argv[1],'r')
lines=f.readlines()

count = 0
for line in lines:
    lines[count] = line.rstrip().split(',')
    count+=1

n= int(lines[0][0])
k1= int(lines[0][1])
instance = [ [int(-1) for i in range(n)]for j in range(n)]
instance[int(lines[1][0])][int(lines[1][1])] = 3
# red car
red_car_i= (int(lines[1][0]),int(lines[1][1])) 

# Storing the initial places of all the horizontal and vertical cars
hori_cars_i=[]
vert_cars_i=[]
mines_i=[]
# Maintaining a count of the number of cars 
hori_cars=0
vert_cars=0
mines=0
for i in range(2,count):
    instance[int(lines[i][1])][int(lines[i][2])] = int(lines[i][0])
    if(int(lines[i][0])==0):
        vert_cars+=1
        vert_cars_i.append((int(lines[i][1]),int(lines[i][2])))
    elif(int(lines[i][0])==1):
        hori_cars+=1
        hori_cars_i.append((int(lines[i][1]),int(lines[i][2])))
    else: 
        mines+=1
        mines_i.append((int(lines[i][1]),int(lines[i][2])))

s= Solver()

possible = False
for k in range(n-red_car_i[1]-2,k1+1):
    s.push()
    
    # Remember H me j wala index is 0th indexing 
    H = [[[Bool("h_%s_%s_%s" %(i,j,m)) for m in range(2)] for j in range(k)]for i in range(hori_cars)] 
    V = [[[Bool("v_%s_%s_%s" %(i,j,m)) for m in range(2)] for j in range(k)]for i in range(vert_cars)]

    # A better int version which stores the cell in which the ith car is present after j moves
    HCd = [[Int("hcd_%s_%s" %(i,j)) for j in range(k+1)] for i in range(hori_cars)] 
    VCd = [[Int("vcd_%s_%s" %(i,j)) for j in range(k+1)] for i in range(vert_cars)] 


    # Red Car:
    R = [[Bool("r_%s_%s" %(j,m)) for m in range(2)] for j in range(k)]
    RCd = [Int("rcd_%s" %(j)) for j in range(k+1)]

    s.add(RCd[k]==n-2)
    #Making sure things dont go out of the grid
    hori_const = [And(HCd[i][j]>=0,HCd[i][j]<n-1)for i in range(hori_cars) for j in range(k+1)]
    vert_const = [And(VCd[i][j]>=0,VCd[i][j]<n-1)for i in range(vert_cars) for j in range(k+1)]
    red_const = [And(RCd[j]>=0,RCd[j]<n-1) for j in range(k+1)]
    s.add(hori_const+vert_const+red_const)
    
    R1 = [(RCd[0] == red_car_i[1])]

    H1 = [HCd[i][0]==hori_cars_i[i][1] for i in range(hori_cars)]

    V1 = [VCd[i][0]==vert_cars_i[i][0] for i in range(vert_cars)]

    s.add(R1)
    s.add(H1)
    s.add(V1)

    # Checking if it really reaches towards the end

    # In every move only one of the car will move in either direction
    for j in range (k):
        HC_moves_1 = [H[i][j][1] for i in range(hori_cars)]
        HC_moves_0 = [H[i][j][0] for i in range(hori_cars)]
        VC_moves_1 = [V[i][j][1] for i in range(vert_cars)]
        VC_moves_0 = [V[i][j][0] for i in range(vert_cars)]
        RC_moves_1 = [R[j][1]]
        RC_moves_0 = [R[j][0]]
        uniq_moves= HC_moves_1+HC_moves_0+VC_moves_0+VC_moves_1+RC_moves_1+RC_moves_0
        s.add(z3.PbEq([(x,1) for x in uniq_moves],1))


    # Propagation move
    # Initialise that 

    # Make a condition ki last - 1 se aage nahi, 0 se piche nahi
    movelimit_H1 = [Implies(HCd[i][j]==n-2,Not(H[i][j][1]))for i in range(hori_cars) for j in range(k)]
    movelimit_H0 = [Implies(HCd[i][j]==0,Not(H[i][j][0]))for i in range(hori_cars) for j in range(k)]
    movelimit_V1 = [Implies(VCd[i][j]==n-2,Not(V[i][j][1]))for i in range(vert_cars) for j in range(k)]
    movelimit_V0 = [Implies(VCd[i][j]==0,Not(V[i][j][0]))for i in range(vert_cars) for j in range(k)]
    movelimit_R1 = [Implies(RCd[j]==n-2,Not(R[j][1])) for j in range(k)]
    movelimit_R0 = [Implies(RCd[j]==0,Not(R[j][0])) for j in range(k)]
    s.add(movelimit_R0)
    s.add(movelimit_R1)
    s.add(movelimit_V0)
    s.add(movelimit_V1)
    s.add(movelimit_H0)
    s.add(movelimit_H1)

    # If a move is played, update it.
    HHr11 = [And(Implies(H[i][j][1],HCd[i][j+1]==HCd[i][j]+1),Implies(Not(H[i][j][1]),Or(HCd[i][j+1]== HCd[i][j],HCd[i][j+1]==HCd[i][j]-1))) for i in range (hori_cars) for j in range(k)]
    HHr12 = [And(Implies(H[i][j][0],HCd[i][j+1]==HCd[i][j]-1),Implies(Not(H[i][j][0]),Or(HCd[i][j+1]== HCd[i][j],HCd[i][j+1]==HCd[i][j]+1))) for i in range (hori_cars) for j in range(k)]

    VVr11 = [And(Implies(V[i][j][1],VCd[i][j+1]==VCd[i][j]+1),Implies(Not(V[i][j][1]),Or(VCd[i][j+1]== VCd[i][j],VCd[i][j+1]==VCd[i][j]-1))) for i in range (vert_cars) for j in range(k)]
    VVr12 = [And(Implies(V[i][j][0],VCd[i][j+1]==VCd[i][j]-1),Implies(Not(V[i][j][0]),Or(VCd[i][j+1]== VCd[i][j],VCd[i][j+1]==VCd[i][j]+1))) for i in range (vert_cars) for j in range(k)]

    RHr1 = [And(Implies(R[j][1],RCd[j+1] - RCd[j] == 1),Implies(Not(R[j][1]),Or(RCd[j+1]==RCd[j],R[j][0],RCd[j+1] - RCd[j] == -1)))for j in range(k)]

    RHr0 = [And(Implies(R[j][0],RCd[j+1] - RCd[j] == -1),Implies(Not(R[j][0]),Or(RCd[j+1]==RCd[j],RCd[j+1] - RCd[j] == 1)))for j in range(k)]

    


    s.add(HHr11)
    s.add(VVr11)
    s.add(VVr12)
    s.add(HHr12)
    s.add(RHr1)
    s.add(RHr0)

    # Making sure that while moving ahead there isn't any mine present : +2 is as the next square will move one step ahead
    HC_and_MINES_1 = [Implies(H[i][j][1],Implies(hori_cars_i[i][0]==mines_i[a][0],HCd[i][j+1]+1 != mines_i[a][1])) for i in range(hori_cars) for j in range(k) for a in range(mines)]
    HC_and_MINES_0 = [Implies(H[i][j][0],Implies(hori_cars_i[i][0]==mines_i[a][0],HCd[i][j+1]!=mines_i[a][1])) for i in range(hori_cars) for j in range(k) for a in range(mines)]

    VC_and_MINES_1 = [Implies(V[i][j][1],Implies(vert_cars_i[i][1]==mines_i[a][1],VCd[i][j+1]+1!=mines_i[a][0])) for i in range(vert_cars) for j in range(k) for a in range(mines)]

    VC_and_MINES_0 = [Implies(V[i][j][0],Implies(vert_cars_i[i][1]==mines_i[a][1],VCd[i][j+1]!=mines_i[a][0])) for i in range(vert_cars) for j in range(k) for a in range(mines)]


    R_and_MINES_1 = [Implies(R[j][1],Implies(red_car_i[0]==mines_i[a][0],RCd[j+1]+1!=mines_i[a][1]))for j in range (k) for a in range(mines)]
    R_and_MINES_0 = [Implies(R[j][0],Implies(red_car_i[0]==mines_i[a][0],RCd[j+1]!=mines_i[a][1]))for j in range (k) for a in range(mines)]


    s.add(HC_and_MINES_1)
    s.add(VC_and_MINES_1)
    s.add(HC_and_MINES_0)
    s.add(VC_and_MINES_0)
    s.add(R_and_MINES_1)
    s.add(R_and_MINES_0)

    # ---------------------------------------------------------------------------------------------------------Correct till now


    # write conditions ki koi bhi car kabhi bhi ekdum bahar wali row/column par nahi hai

    # Making sure a horizontal move doesn't affect the horizontal cars: if there is no 
    # add a condition to check whether a next car is even possible there
    # Position of the moving car is set,the position of the right car is : +2
    # Store the HC as Int i.e. between (0->n-1) to specify the position 


    # |L1|L2| |
    # the Horizontal moved car has a car part colliding    ----- Try converting the condition to if else it will take place fast
    HC_and_HC_1 = [Implies(H[i][j][1],Implies(hori_cars_i[a][0]==hori_cars_i[i][0],HCd[i][j+1]+1!=HCd[a][j+1])) for j in range(k) for i in range(hori_cars) for a in range(hori_cars) ]
    HC_and_HC_0 = [Implies(H[i][j][0],Implies(hori_cars_i[a][0]==hori_cars_i[i][0],HCd[i][j+1]-1!=HCd[a][j+1])) for j in range(k) for i in range(hori_cars) for a in range(hori_cars) ]

    VC_and_VC_1 = [Implies(V[i][j][1],Implies(vert_cars_i[a][1]==vert_cars_i[i][1],VCd[i][j+1]+1!=VCd[a][j+1])) for j in range(k) for i in range(vert_cars) for a in range(vert_cars) ]
    VC_and_VC_0 = [Implies(V[i][j][0],Implies(vert_cars_i[a][1]==vert_cars_i[i][1],VCd[i][j+1]-1!=VCd[a][j+1])) for j in range(k) for i in range(vert_cars) for a in range(vert_cars) ]

    RC_and_HC_1 = [Implies(R[j][1],Implies(hori_cars_i[a][0]==red_car_i[0],RCd[j+1]+1!=HCd[a][j+1])) for j in range(k) for a in range(hori_cars) ]
    RC_and_HC_0 = [Implies(R[j][0],Implies(hori_cars_i[a][0]==red_car_i[0],RCd[j+1]-1!=HCd[a][j+1])) for j in range(k) for a in range(hori_cars) ]

    HC_and_RC_1 = [Implies(H[i][j][1],Implies(hori_cars_i[i][0]==red_car_i[0],HCd[i][j+1]+1!=RCd[j+1]))for j in range(k) for i in range(hori_cars)]
    HC_and_RC_0 = [Implies(H[i][j][0],Implies(hori_cars_i[i][0]==red_car_i[0],HCd[i][j+1]-1!=RCd[j+1]))for j in range(k) for i in range(hori_cars)]
    s.add(HC_and_HC_0)
    s.add(HC_and_HC_1)
    s.add(VC_and_VC_0)
    s.add(VC_and_VC_1)
    s.add(RC_and_HC_0)
    s.add(RC_and_HC_1)
    s.add(HC_and_RC_0)
    s.add(HC_and_RC_1)

    # Horizontal movement with vertical cars
    HC_and_VC_1 = [Implies(H[i][j][1],Implies(vert_cars_i[a][1]==HCd[i][j+1]+1,And(VCd[a][j+1]!=hori_cars_i[i][0],(VCd[a][j+1]+1)!=hori_cars_i[i][0]))) for i in range(hori_cars) for j in range(k)for a in range(vert_cars)]
    HC_and_VC_0 = [Implies(H[i][j][0],Implies(vert_cars_i[a][1]==HCd[i][j+1],And(VCd[a][j+1]!=hori_cars_i[i][0],(VCd[a][j+1]+1)!=hori_cars_i[i][0]))) for i in range(hori_cars) for j in range(k)for a in range(vert_cars)]


    VC_and_HC_1 = [Implies(V[i][j][1],Implies(hori_cars_i[a][0]==VCd[i][j+1]+1,And(HCd[a][j+1]!=vert_cars_i[i][1],(HCd[a][j+1]+1)!=vert_cars_i[i][1]))) for i in range(vert_cars) for j in range(k)for a in range(hori_cars)]
    VC_and_HC_0 = [Implies(V[i][j][0],Implies(hori_cars_i[a][0]==VCd[i][j+1],And(HCd[a][j+1]!=vert_cars_i[i][1],(HCd[a][j+1]+1)!=vert_cars_i[i][1]))) for i in range(vert_cars) for j in range(k) for a in range(hori_cars)]

    RC_and_VC_1 = [Implies(R[j][1],Implies(vert_cars_i[a][1]==RCd[j+1]+1,And(VCd[a][j+1]!=red_car_i[0],(VCd[a][j+1]+1)!=red_car_i[0])))  for a in range(vert_cars) for j in range(k)]
    RC_and_VC_0 = [Implies(R[j][0],Implies(vert_cars_i[a][1]==RCd[j+1],And(VCd[a][j+1]!=red_car_i[0],(VCd[a][j+1]+1)!=red_car_i[0]))) for a in range(vert_cars) for j in range(k)]

    VC_and_RC_1 = [Implies(V[i][j][1],Implies(red_car_i[0]==VCd[i][j+1]+1,And(RCd[j+1]!=vert_cars_i[i][1],RCd[j+1]+1!=vert_cars_i[i][1])))for i in range(vert_cars) for j in range(k)]
    VC_and_RC_0 = [Implies(V[i][j][0],Implies(red_car_i[0]==VCd[i][j+1],And(RCd[j+1]!=vert_cars_i[i][1],RCd[j+1]+1!=vert_cars_i[i][1])))for i in range(vert_cars) for j in range(k)]
    s.add(HC_and_VC_1)
    s.add(VC_and_HC_1)
    s.add(RC_and_VC_1)
    s.add(VC_and_RC_1)

    s.add(HC_and_VC_0)
    s.add(VC_and_HC_0)
    s.add(RC_and_VC_0)
    s.add(VC_and_RC_0)

    satisfy=s.check()
    if(satisfy==sat):
        m=s.model()
        temp=[]
        for i in range(k):
            for j in range(vert_cars):
                if m.evaluate(V[j][i][1])==True :
                    temp+=[(m.evaluate(VCd[j][i+1]),vert_cars_i[j][1])]
                elif m.evaluate(V[j][i][0])==True:
                    temp+=[(m.evaluate(VCd[j][i+1]+1),vert_cars_i[j][1])]
            for j in range(hori_cars):
                if m.evaluate(H[j][i][1])==True:
                    temp+=[(hori_cars_i[j][0],m.evaluate(HCd[j][i+1]))]
                elif m.evaluate(H[j][i][0])==True:
                    temp+=[(hori_cars_i[j][0],m.evaluate(HCd[j][i+1]+1))]
            if m.evaluate(R[i][1])==True: 
                temp+=[(red_car_i[0],m.evaluate(RCd[i+1]))]
            elif m.evaluate(R[i][0])==True:
                temp+=[(red_car_i[0],m.evaluate(RCd[i+1]+1))]
        for a,b in temp:
            print(str(a)+','+str(b))
        possible=True
        break
    else:
        s.pop()
if(not possible):
   print('unsat')